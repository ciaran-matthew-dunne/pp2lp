open Syntax_pp

module P = Proof_tree
module L = Lp_tree

(* Translation context.

   `hyps` carries the predicate each `_hN` was introduced with; hyp-search
   rules (AXM1-6, IMP5, EAXM1, EAXM2) look up the predicate they need by
   structural equality.

   `xs` carries the PP-side variable names each `_xN` corresponds to (the
   binder's vars at the point we entered it). Witness-search rules (AXM9,
   NRM19) substitute those names into the rule's expected hypothesis
   pattern and look it up in `hyps`. *)
type ctx = {
  mutable n : int;
  mutable hyps : (string * prd) list;
  mutable xs : (string * string list) list;
}

let create_ctx () = { n = 0; hyps = []; xs = [] }

let fresh_h ctx pred =
  ctx.n <- ctx.n + 1;
  let h = Printf.sprintf "_h%d" ctx.n in
  ctx.hyps <- (h, pred) :: ctx.hyps;
  h

let fresh_x ctx pp_vars =
  ctx.n <- ctx.n + 1;
  let x = Printf.sprintf "_x%d" ctx.n in
  ctx.xs <- (x, pp_vars) :: ctx.xs;
  x

(* Allocate a fresh `_xN` name without registering in ctx.xs. Used for
   chain-internal binders: the chain's `assume v` keeps v scoped to the
   chain block, and the sibling cont mustn't see it as an in-scope tuple
   var. *)
let fresh_x_local ctx =
  ctx.n <- ctx.n + 1;
  Printf.sprintf "_x%d" ctx.n

let with_x ctx x pp_vars f =
  let saved = ctx.xs in
  ctx.xs <- (x, pp_vars) :: ctx.xs;
  Fun.protect ~finally:(fun () -> ctx.xs <- saved) f

let scoped_hyps ctx f =
  let saved_h = ctx.hyps in
  let saved_x = ctx.xs in
  Fun.protect ~finally:(fun () ->
    ctx.hyps <- saved_h;
    ctx.xs <- saved_x) f

let base = Rule_db.base_of

(* ---- Goal extraction from rule annotations ---- *)

let goal_of_anno = function
  | Some rhs -> Some (prd_of_rhs rhs)
  | None -> None

let antecedent_of = function
  | Binary (Imp, ant, _) -> Some ant
  | _ -> None

let binder_vars_of = function
  | Bind (_, vs, _) -> Some vs
  | _ -> None

let is_true_atom = function
  | Lift (Var ("VRAI" | "TRUE")) -> true
  | _ -> false

(* ---- Hyp lookup: derive the needed predicate from the goal ----

   Each `dynamic:hyp` rule has a fixed LP-type signature; the hypothesis
   it expects is a function of the goal. This table mirrors the signatures
   in lp/rules/Axm.lp, Impl.lp, Eq.lp. *)

let expected_hyp_pred rule goal =
  match base rule, goal with
  | "AXM1", Binary (Imp, p, _) -> Some (Unary (Not, p))
  | "AXM2", Binary (Imp, Unary (Not, p), _) -> Some p
  | "AXM3", p -> Some p
  | "AXM4", Binary (Imp, _, r) -> Some r
  | "AXM5", Binary (Imp, _, Binary (Imp, q, _)) -> Some (Unary (Not, q))
  | "AXM6", Binary (Imp, _, Binary (Imp, Unary (Not, q), _)) -> Some q
  | "IMP5", Binary (Imp, _, q) -> Some q
  | "EAXM1", Binary (Imp, Eq (e, f), _) ->
    (* lp/rules/Eq.lp EAXM1 expects π (¬ (F = E)) — the swap is in the spec *)
    Some (Unary (Not, Eq (f, e)))
  | "EAXM2", Binary (Imp, Unary (Not, Eq (e, f)), _) ->
    Some (Eq (f, e))
  | _ -> None

let find_hyp_by_pred ctx pred =
  List.find_map
    (fun (name, p) -> if p = pred then Some name else None) ctx.hyps

(* ---- Alpha + universal-binder-kind-insensitive predicate equality ----

   PP normalisation produces the same propositional content under different
   universal binders — `!` (Bang), `forall` (Forall), `forall2` (Forall2) —
   and with different bound-variable names.  All three map to the single LP
   `!!` (the user aliased `♢`/`♡` to it), so two such predicates have the
   *same* LP type.  Canonicalise to De Bruijn levels and fold the universal
   binders into one kind, then compare structurally.  Used by the INS leaf
   search so a needed conjunct like `!x.¬(⊤ ∧ P x)` matches an in-scope hyp
   written `forall2 y.¬(⊤ ∧ P y)`. *)
let canon_binder = function
  | Bang | Forall | Forall2 -> Forall
  | Exists -> Exists

let rec canon_exp env = function
  | Var s -> (match List.assoc_opt s env with Some n -> Var n | None -> Var s)
  | Nat n -> Nat n
  | App (f, args) -> App (f, List.map (canon_exp env) args)
  | AOp (op, a, b) -> AOp (op, canon_exp env a, canon_exp env b)
  | Neg e -> Neg (canon_exp env e)
  | SetImage (a, b) -> SetImage (canon_exp env a, canon_exp env b)
  | Inter (a, b) -> Inter (canon_exp env a, canon_exp env b)
  | Union (a, b) -> Union (canon_exp env a, canon_exp env b)

let rec canon_prd depth env = function
  | Lift e -> Lift (canon_exp env e)
  | Unary (op, p) -> Unary (op, canon_prd depth env p)
  | Binary (op, a, b) -> Binary (op, canon_prd depth env a, canon_prd depth env b)
  | Mem (es, e) -> Mem (List.map (canon_exp env) es, canon_exp env e)
  | Eq (a, b) -> Eq (canon_exp env a, canon_exp env b)
  | Leq (a, b) -> Leq (canon_exp env a, canon_exp env b)
  | Bind (k, xs, body) ->
    let names = List.mapi (fun i _ -> Printf.sprintf "#%d" (depth + i)) xs in
    let env' = List.map2 (fun x n -> (x, n)) xs names @ env in
    Bind (canon_binder k, names, canon_prd (depth + List.length xs) env' body)

let prd_equiv a b = canon_prd 0 [] a = canon_prd 0 [] b

let find_hyp_by_equiv ctx pred =
  List.find_map
    (fun (name, p) -> if prd_equiv p pred then Some name else None) ctx.hyps

(* ---- Witness + hyp lookup for AXM9 / NRM19 ----

   AXM9 (`P v ⇒ Q`): the antecedent is `P v` for some witness v of
   tuple arity n. The hypothesis we need is `(`!! u, ¬ (⊤ ∧ P u))`.
   Iterate witnesses (each tracking its binder's pp-vars), substitute
   into each candidate hypothesis's `!!` body, compare to `P v`.

   NRM19 (`(`♡ u, ¬ (⊤ ∧ R u)) ⇒ Q`): the binder's vars and body R
   come from the goal. For each witness, substitute and look up `R v`
   directly in hyps. *)

(* AXM9 expects an `!!`-form hypothesis (LP-side `π (`!! u, ¬ (⊤ ∧ P u))`).
   On the PP-AST side, the same propositional content can appear under any
   of the universal binders — `!` (`Bang`), `forall` (`Forall`), or
   `forall2` (`Forall2`) — depending on which normalisation chain produced
   it. Accept all three. *)
let axm9_hyp_shape = function
  | Bind ((Bang | Forall | Forall2), vars,
          Unary (Not, Binary (And, t, p))) when is_true_atom t ->
    Some (vars, p)
  | _ -> None

(* Expand an xs entry into candidate (lp_witness, pp_vars) pairs.
   Whole tuple first, then individual components via prj. *)
let witness_candidates (x_name, x_pp_vars) =
  let whole = (L.Name x_name, x_pp_vars) in
  if List.length x_pp_vars <= 1 then [whole]
  else
    let components = List.mapi (fun i pp_var ->
      (L.App ("prj", [L.Raw (string_of_int i); L.Name x_name]), [pp_var])
    ) x_pp_vars in
    whole :: components

let find_axm9_match ctx goal =
  match antecedent_of goal with
  | None -> None
  | Some p_v ->
    let try_candidate (lp_witness, pp_vars) (h_name, h_pred) =
      match axm9_hyp_shape h_pred with
      | Some (h_vars, h_body)
        when List.length h_vars = List.length pp_vars ->
        let env = List.map2 (fun v pp -> (v, Var pp)) h_vars pp_vars in
        if subst_prd env h_body = p_v then Some (lp_witness, h_name)
        else None
      | _ -> None
    in
    List.find_map (fun x ->
      List.find_map (fun cand ->
        List.find_map (try_candidate cand) ctx.hyps
      ) (witness_candidates x)
    ) ctx.xs

let find_nrm19_match ctx goal =
  match goal with
  | Binary (Imp, Bind (Forall2, vars, Unary (Not, Binary (And, t, r_body))), _)
    when is_true_atom t ->
    let try_candidate (lp_witness, pp_vars) =
      if List.length pp_vars <> List.length vars then None
      else
        let env = List.map2 (fun v pp -> (v, Var pp)) vars pp_vars in
        let needed = subst_prd env r_body in
        match find_hyp_by_pred ctx needed with
        | Some h_name -> Some (lp_witness, h_name)
        | None -> None
    in
    List.find_map (fun x ->
      List.find_map try_candidate (witness_candidates x)
    ) ctx.xs
  | _ -> None

(* ---- INS: universal-instantiation contradiction search ----

   INS arises when PP's instantiation phase discovers that universal
   hypotheses in H, together with simple hypotheses, form a
   contradiction.  The replay child is always AXM7 (⊥ ⇒ ⊥) —
   redundant once we have the evidence.

   Evidence term:  !!_to_pi _ h_univ witness (∧ᵢ h₁ … hₙ)
   where h_univ is a normalised universal  ∀x · ¬(P₁(x) ∧ … ∧ Pₙ(x)),
   witness is a tuple variable, and each hᵢ matches Pᵢ(witness).

   Generalises find_axm9_match from "one non-trivial conjunct after ⊤"
   to "N conjuncts, all matched".  *)

let ins_hyp_shape = function
  | Bind ((Bang | Forall | Forall2), vars, Unary (Not, body)) ->
    Some (vars, body)
  | _ -> None

let conj_intro = "\xe2\x8b\x80_intro"           (* ⋀_intro *)
let conj_nil_prf = "\xe2\x8b\x80_nil_prf"       (* ⋀_nil_prf *)
let true_intro = "\xe2\x8a\xa4\xe1\xb5\xa2"     (* ⊤ᵢ *)

let collect_conj_leaves = Pp_lp.conj_leaves

(* Build a ⋀-form evidence term from a list of leaf proofs.
   Snoc left-fold bottoming in ⋀_nil_prf:
   ⋀_intro (… (⋀_intro ⋀_nil_prf ev₀) …) evₙ₋₁
   ⋀_intro's list/elt implicits are inferred from the expected type. *)
let rec build_conj_chain_rev = function
  | [] -> L.Name conj_nil_prf
  | ev :: rest ->
    L.App (conj_intro, [build_conj_chain_rev rest; ev])

let build_conj_chain evs = build_conj_chain_rev (List.rev evs)

let leaf_evidence ctx env leaf =
  if is_true_atom leaf then Some (L.Name true_intro)
  else
    let needed = subst_prd env leaf in
    (* Match up to alpha + universal-binder kind: a conjunct may be a
       universal (e.g. the "no image" `!x.¬(⊤ ∧ …)` of a totality goal)
       whose in-scope hyp uses a different binder/var but the same LP type. *)
    match find_hyp_by_equiv ctx needed with
    | Some h -> Some (L.Name h)
    | None -> None

let match_conj ctx env body =
  let leaves = collect_conj_leaves body in
  let opt_evs = List.map (leaf_evidence ctx env) leaves in
  if List.for_all Option.is_some opt_evs then
    Some (build_conj_chain (List.map Option.get opt_evs))
  else None

let find_ins_contradiction ctx =
  let try_candidate (lp_witness, pp_vars) (h_name, h_pred) =
    match ins_hyp_shape h_pred with
    | Some (h_vars, h_body)
      when List.length h_vars = List.length pp_vars ->
      let env = List.map2 (fun v pp -> (v, Var pp)) h_vars pp_vars in
      (match match_conj ctx env h_body with
       | Some conj_ev ->
         Some (L.Refine ("!!_to_pi",
           [L.Hole; L.Name h_name; lp_witness; conj_ev]))
       | None -> None)
    | _ -> None
  in
  List.find_map (fun x ->
    List.find_map (fun cand ->
      List.find_map (try_candidate cand) ctx.hyps
    ) (witness_candidates x)
  ) ctx.xs

(* ---- Dispatch helpers (args for non-hyp-search rules) ---- *)

let emit_words rule =
  match Rule_db.emit_args rule with
  | None -> []
  | Some spec ->
    String.split_on_char ' ' spec |> List.filter ((<>) "")

let is_trust_spec rule =
  match emit_words rule with
  | [] -> false
  | words -> List.for_all ((=) "trust") words

(* ---- Tuple-projection rendering of rule arguments ----

   Rule arguments carrying a predicate/expression (AR9/AR3/AR10 solver
   results) may mention PP variables bound by an enclosing ALL8/ALL7
   binder.  In LP those binders introduce a single `Tuple n` value, so var
   k of tuple `x` must render as `prj k x` — exactly the env the n-ary
   quantifier kernel uses.  Build that env from `ctx.xs` and pre-render to
   a `Raw` term.  (With no in-scope binder the env is empty and these
   render identically to `L.Pred` / `L.Exp`.) *)
let pp_env_of ctx =
  List.concat_map (fun (x_name, pp_vars) ->
    List.mapi (fun i v -> (v, (i, x_name))) pp_vars
  ) ctx.xs

let render_pred_term ctx prd =
  let buf = Buffer.create 64 in
  Buffer.add_char buf '(';
  Pp_lp.pp_prd ~env:(pp_env_of ctx) buf prd;
  Buffer.add_char buf ')';
  L.Raw (Buffer.contents buf)

let render_exp_term ctx e =
  let buf = Buffer.create 64 in
  Buffer.add_char buf '(';
  Pp_lp.pp_exp ~env:(pp_env_of ctx) buf e;
  Buffer.add_char buf ')';
  L.Raw (Buffer.contents buf)

let dynamic_value_args ctx rule arg =
  match Rule_db.emit_args rule, arg with
  | Some "dynamic:ar3", Some (PipeArg (a, _b)) -> [render_exp_term ctx a]
  | Some "dynamic:ar9", Some (Pred p) -> [render_pred_term ctx p]
  | _, _ -> []

let metadata_extra_args rule =
  match Rule_db.emit_args rule with
  | None -> []
  | Some "dynamic:ar9" ->
    (* AR9 (F) : π (E = F) → π ((F ≤ 𝟎) ⇒ R) → π ((E ≤ 𝟎) ⇒ R).
       After the F expression (a dynamic value arg) comes the solver-confirmed
       equality E = F — supply `trust` for it; the Seq slot (the F ≤ 𝟎 ⇒ R
       continuation) is the remaining hole. *)
    [L.Trust]
  | Some "dynamic:ar3"
  | Some "dynamic:ar10"
  | Some "dynamic:hyp" -> []
  | Some "dynamic:axm9"
  | Some "dynamic:nrm19" -> [L.Hole; L.Hole]
  | Some _ when is_trust_spec rule -> []
  | Some _ -> [L.Hole]

let slot_hole_args rule =
  let trusts = ref (emit_words rule) in
  Rule_db.slots rule
  |> List.map (function
    | Rule_db.Con ->
      (match !trusts with
       | "trust" :: rest -> trusts := rest; L.Trust
       | _ -> L.Hole)
    | Rule_db.Seq | Rule_db.Res -> L.Hole)

let default_rule_args ctx rule arg =
  dynamic_value_args ctx rule arg @ metadata_extra_args rule @ slot_hole_args rule

let replace_last args last =
  match List.rev args with
  | [] -> [last]
  | _ :: rest -> List.rev (last :: rest)

(* ---- Conjunction helpers ---- *)

let conjuncts = Pp_lp.conj_children_left

let find_conjunct_pos conjs target =
  let rec loop i = function
    | [] -> None
    | c :: rest -> if c = target then Some i else loop (i + 1) rest
  in
  loop 0 conjs

let find_and5_pair conjs =
  let arr = Array.of_list conjs in
  let n = Array.length arr in
  let result = ref None in
  for j = 0 to n - 1 do
    if !result = None then
      match arr.(j) with
      | Binary (Imp, p, _) ->
        (* First try: match whole antecedent as one element *)
        let found_whole = ref None in
        for k = 0 to n - 1 do
          if !found_whole = None && k <> j && arr.(k) = p then
            found_whole := Some [k]
        done;
        (match !found_whole with
         | Some positions -> result := Some (positions, j)
         | None ->
           (* Second try: match antecedent's leaves individually *)
           let ant_leaves = Pp_lp.conj_leaves p in
           let used = Array.make n false in
           used.(j) <- true;
           let positions = List.filter_map (fun leaf ->
             let rec find k =
               if k >= n then None
               else if not used.(k) && arr.(k) = leaf then
                 (used.(k) <- true; Some k)
               else find (k + 1)
             in find 0
           ) ant_leaves in
           if List.length positions = List.length ant_leaves then
             result := Some (positions, j))
      | _ -> ()
  done;
  !result

(* ---- Per-rule tactic emission ---- *)

let tactic_for_hyp ctx rule arg anno =
  let default_args = default_rule_args ctx rule arg in
  let fallback = L.Refine (rule, default_args) in
  match goal_of_anno anno with
  | None -> fallback
  | Some goal ->
    match expected_hyp_pred rule goal with
    | None -> fallback
    | Some needed ->
      match find_hyp_by_pred ctx needed with
      | Some name ->
        L.Refine (rule, replace_last default_args (L.Name name))
      | None -> fallback

let tactic_for_witness_hyp ctx rule anno =
  let fallback = L.Refine (rule, [L.Hole; L.Hole]) in
  match goal_of_anno anno with
  | None -> fallback
  | Some goal ->
    let result =
      match base rule with
      | "AXM9" -> find_axm9_match ctx goal
      | "NRM19" -> find_nrm19_match ctx goal
      | _ -> None
    in
    match result with
    | Some (witness, h) -> L.Refine (rule, [witness; L.Name h])
    | None -> fallback

let tactic_for_axm8 ctx rule anno =
  let fallback = L.Refine (rule, [L.Hole]) in
  match goal_of_anno anno with
  | Some (Binary (Imp, lhs, rhs)) ->
    let conjs = conjuncts lhs in
    (match find_conjunct_pos conjs rhs with
     | Some k ->
       ctx.n <- ctx.n + 1;
       let h = Printf.sprintf "_h%d" ctx.n in
       let buf = Buffer.create 64 in
       Pp_lp.emit_extract buf h conjs k;
       L.Refine (rule, [L.Lambda (h, None, L.Raw (Buffer.contents buf))])
     | None -> fallback)
  | _ -> fallback

let tactic_for_rule ctx rule arg anno children =
  match Rule_db.emit_args rule with
  | Some "dynamic:hyp" when children = [] -> tactic_for_hyp ctx rule arg anno
  | Some "dynamic:axm8" when children = [] -> tactic_for_axm8 ctx rule anno
  | Some "dynamic:axm9" when children = [] ->
    tactic_for_witness_hyp ctx rule anno
  | Some "dynamic:nrm19" -> tactic_for_witness_hyp ctx rule anno
  | Some "dynamic:ar10" ->
    (* AR10 [P Q R] : π (P = Q) → π (Q ⇒ R) → π (P ⇒ R).
       Supply Q explicitly so Lambdapi can type the `trust` equality.
       Q may mention enclosing-binder vars, so render it with the
       tuple-projection env rather than the raw PP names. *)
    (match arg with
     | Some (Pred q) ->
       L.Refine ("@AR10", [L.Hole; render_pred_term ctx q; L.Hole; L.Trust; L.Hole])
     | _ -> L.Refine (rule, [L.Trust; L.Hole]))
  | _ -> L.Refine (rule, default_rule_args ctx rule arg)

let rec tree ctx = function
  | P.Apply { rule; children = [c]; _ }
    when Rule_db.is_hoas_identity (base rule) ->
    tree ctx c
  | P.Apply { rule; anno; children = [c]; _ }
    when base rule = "AND5" ->
    (match goal_of_anno anno with
     | Some (Binary (Imp, lhs, _)) ->
       let conjs = Pp_lp.conj_children_left lhs in
       (match find_and5_pair conjs with
        | Some (ant_positions, j) ->
          ctx.n <- ctx.n + 1;
          let h = Printf.sprintf "_h%d" ctx.n in
          let buf = Buffer.create 64 in
          Pp_lp.emit_and5_fwd buf h conjs ant_positions j;
          let fwd = L.Lambda (h, None, L.Raw (Buffer.contents buf)) in
          L.Then (L.Refine ("AND5", [fwd; L.Hole]), tree ctx c)
        | None -> default ctx rule None anno [c])
     | _ -> default ctx rule None anno [c])
  | P.Apply { rule; arg; anno; children = [_]; _ }
    when Rule_db.emit_args rule = Some "dynamic:nrm19" ->
    (* PP's NRM19 child is a placeholder (VR4 / ⊤) — the LP encoding
       discharges the implication directly via the witness/hypothesis
       pair, no premise to thread. Drop the child. *)
    L.Step (tactic_for_rule ctx rule arg anno [])
  | P.Apply { rule; children = [_]; _ }
    when base rule = "INS" ->
    (match find_ins_contradiction ctx with
     | Some tactic -> L.Step tactic
     | None ->
       failwith "translate: INS contradiction search failed — \
         no universal hypothesis × witness pair matches all conjuncts \
         (likely arithmetic-rewritten hypotheses)")
  | P.Apply { rule; anno; children = [c0; c1]; _ }
    when base rule = "ALL7" || base rule = "XST8" ->
    branching ctx rule anno c0 c1
  | P.Apply { rule; arg; anno; children; _ } ->
    default ctx rule arg anno children

and default ctx rule arg anno children =
  let goal = goal_of_anno anno in
  match children with
  | [c] when base rule = "OPR1" || base rule = "OPR2" ->
    (* OPR1: (x = E) ⇒ P x — assume the equality and rewrite x ↦ E.
       OPR2: (E = x) ⇒ P x — same but rewrite right-to-left. *)
    let eq_pred =
      match goal with
      | Some (Binary (Imp, eq, _)) -> eq
      | _ -> failwith (Printf.sprintf
          "translate: %s expected an implication annotation (got non-⇒ goal)" rule)
    in
    let h = fresh_h ctx eq_pred in
    let rtl = base rule = "OPR2" in
    L.Assume (h,
      L.Then (L.Rewrite { try_ = true; rtl; name = h }, tree ctx c))
  | _ ->
    let tactic = tactic_for_rule ctx rule arg anno children in
    match children with
    | [] -> L.Step tactic
    | [c] when Rule_db.intro_antecedent rule ->
      let ant =
        match goal with
        | Some (Binary (Imp, ant, _)) -> ant
        | _ -> failwith (Printf.sprintf
          "translate: %s (intro-antecedent) expected an implication annotation" rule)
      in
      let h = fresh_h ctx ant in
      L.Assume_then (tactic, h, tree ctx c)
    | [c] when base rule = "ALL8" ->
      let pp_vars =
        match goal with
        | Some g -> Option.value ~default:[] (binder_vars_of g)
        | None -> []
      in
      let x = fresh_x ctx pp_vars in
      L.Assume_then (tactic, x, tree ctx c)
    | [c] ->
      let child = tree ctx c in
      L.Then (tactic, child)
    | [c0; c1] ->
      let left = scoped_hyps ctx (fun () -> tree ctx c0) in
      let right = scoped_hyps ctx (fun () -> tree ctx c1) in
      L.Branches (tactic, left, right)
    | _ ->
      failwith (Printf.sprintf
        "translate: %s arity %d unsupported"
        rule (List.length children))

and branching ctx rule anno chain_node cont =
  let goal = goal_of_anno anno in
  let pp_vars =
    match base rule, goal with
    | "ALL7", Some (Binary (Imp, b, _)) ->
      Option.value ~default:[] (binder_vars_of b)
    | "XST8", Some g ->
      Option.value ~default:[] (binder_vars_of g)
    | _ -> []
  in
  let quant_sym = if base rule = "ALL7" then "ALL7" else "XST8" in
  let tactic = L.Refine (quant_sym, [L.Hole; L.Hole]) in
  (* The chain's bound v is in lambdapi scope inside the chain block
     only — the cont's `(`♢ v, …)` keeps v internal to the quantifier.
     Allocate v without registering, then register only inside the
     chain's scoped block. *)
  let v = fresh_x_local ctx in
  let chain_proof = scoped_hyps ctx (fun () ->
    with_x ctx v pp_vars (fun () ->
      L.Assume (v, chain_tree ctx chain_node)))
  in
  let cont_proof = scoped_hyps ctx (fun () -> tree ctx cont) in
  L.Branches (tactic, chain_proof, cont_proof)

(* The Res-chain handed to ALL7/XST8 has type `Π v : Tuple n, Res (P v)`,
   so it must be entered as a subproof: `assume v` binds the tuple at its
   correct (Lambdapi-inferred) type, and each chain step is then a `refine`
   in sequence — just like the regular proof tree, but with the primed
   Res-typed rule forms. *)
and chain_tree ctx = function
  | P.Apply { rule; children = []; arg; _ } ->
    let args = dynamic_value_args ctx rule arg @ slot_hole_args rule in
    L.Step (L.Refine (rule, args))
  | P.Apply { rule; anno; children = [c]; _ } when base rule = "ALL8" ->
    let pp_vars =
      match goal_of_anno anno with
      | Some g -> Option.value ~default:[] (binder_vars_of g)
      | None -> []
    in
    let x = fresh_x ctx pp_vars in
    let tactic = L.Refine (rule, [L.Hole]) in
    L.Assume_then (tactic, x, chain_tree ctx c)
  | P.Apply { rule; anno; children = [c]; _ }
    when base rule = "OPR1" || base rule = "OPR2" ->
    let pp_env = List.concat_map (fun (x_name, pp_vars) ->
      List.mapi (fun i v -> (v, (i, x_name))) pp_vars
    ) ctx.xs in
    let render_pred prd =
      let buf = Buffer.create 128 in
      Pp_lp.pp_prd ~env:pp_env buf prd;
      Buffer.contents buf
    in
    (* Bind a fresh `_xN` (PP vars never start with `_`, so it cannot be
       captured by a variable already free in `consequent`). *)
    let z = fresh_x_local ctx in
    let p_lambda =
      match goal_of_anno anno with
      | Some (Binary (Imp, Eq (lhs, _rhs), consequent))
        when base rule = "OPR1" ->
        (match lhs with
         | Var v ->
           L.Lambda (z, Some L.Tau_i,
             L.Raw (render_pred (subst_prd [(v, Var z)] consequent)))
         | _ -> L.Hole)
      | Some (Binary (Imp, Eq (_lhs, rhs), consequent))
        when base rule = "OPR2" ->
        (match rhs with
         | Var v ->
           L.Lambda (z, Some L.Tau_i,
             L.Raw (render_pred (subst_prd [(v, Var z)] consequent)))
         | _ -> L.Hole)
      | _ -> L.Hole
    in
    let tactic = L.Refine (rule, [p_lambda] @ slot_hole_args rule) in
    L.Then (tactic, chain_tree ctx c)
  | P.Apply { rule; arg; children = [c]; _ }
    when Rule_db.emit_args rule = Some "dynamic:ar10" ->
    (* AR10_1 [P Q R] (heq : P = Q) (r : Res (Q ⇒ R)) : Res (P ⇒ R).
       Q is the solver result and can't be inferred from P ⇒ R alone, so
       supply it explicitly (env-rendered) with `trust` for the equality;
       the chain continuation fills the Res hole.  Mirrors the main-tree
       AR10 dispatch. *)
    let q_term = match arg with
      | Some (Pred q) -> render_pred_term ctx q
      | _ -> L.Hole
    in
    let tactic =
      L.Refine ("@" ^ rule, [L.Hole; q_term; L.Hole; L.Trust; L.Hole])
    in
    L.Then (tactic, chain_tree ctx c)
  | P.Apply { rule; arg; children = [c]; _ } ->
    let tactic =
      L.Refine (rule, dynamic_value_args ctx rule arg @ slot_hole_args rule)
    in
    L.Then (tactic, chain_tree ctx c)
  | P.Apply { rule; anno; children = [c0; c1]; _ }
    when base rule = "ALL7" || base rule = "XST8" ->
    (* ALL7_1 / XST8_1 inside a Res chain: a per-tuple Res chain ρ (under
       the bound v) plus the continuation r.  Mirrors `branching` but stays
       in Res mode — the ρ child must bind v, exactly like the main-tree
       form, otherwise its `Π v, Res …` goal is left unproven. *)
    let pp_vars =
      match base rule, goal_of_anno anno with
      | "ALL7", Some (Binary (Imp, b, _)) ->
        Option.value ~default:[] (binder_vars_of b)
      | "XST8", Some g ->
        Option.value ~default:[] (binder_vars_of g)
      | _ -> []
    in
    let tactic = L.Refine (rule, [L.Hole; L.Hole]) in
    let v = fresh_x_local ctx in
    let rho = scoped_hyps ctx (fun () ->
      with_x ctx v pp_vars (fun () -> L.Assume (v, chain_tree ctx c0)))
    in
    let cont = scoped_hyps ctx (fun () -> chain_tree ctx c1) in
    L.Branches (tactic, rho, cont)
  | P.Apply { rule; arg; children = [c0; c1]; _ } ->
    let tactic =
      L.Refine (rule, dynamic_value_args ctx rule arg @ slot_hole_args rule)
    in
    let left = scoped_hyps ctx (fun () -> chain_tree ctx c0) in
    let right = scoped_hyps ctx (fun () -> chain_tree ctx c1) in
    L.Branches (tactic, left, right)
  | P.Apply { rule; children; _ } ->
    failwith (Printf.sprintf
      "translate: chain %s arity %d unsupported"
      rule (List.length children))

let translate (pp_tree : P.pp_tree) : L.t =
  tree (create_ctx ()) pp_tree
