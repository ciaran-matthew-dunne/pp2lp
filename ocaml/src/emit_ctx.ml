(* Emission context and the lookups over it.

   This is the bottom layer of the emitter: the mutable proof-construction
   state ([ctx]), the small goal/annotation helpers shared by every layer,
   and the hypothesis / witness / INS searches that read the context.  The
   per-rule tactic construction lives above it in [Rule_emit]; the proof-tree
   walker on top of that in [Translate]. *)

open Syntax_pp

module L = Lp_tree

(* Translation context.

   `hyps` carries the predicate each `_hN` was introduced with; the
   [Hyp_search] rules (AXM1-6, EAXM1, EAXM2) look up the predicate they
   need by structural equality.

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

(* PP primes most rules inside a first-normalisation chain (ALL7_1, ALL9_1,
   STOP_1, IMP4_1…) but leaves NRM rules *unprimed* (it emits `[NRM14]`, not
   `[NRM14_1]`).  In a Res chain those must be the Res-typed `_1` form, so prime
   an unprimed NRM rule name when emitting it in `chain_tree`.  Metadata lookups
   keep using the base name (`base_of "NRM14_1" = "NRM14"`).  Only NRM14_1 has an
   LP symbol so far; other NRM-in-chain rules fail loud, surfacing the need. *)
let chain_emit_name rule =
  if Rule_db.is_nrm rule && not (Rule_db.is_primed rule)
  then rule ^ "_1" else rule

(* ---- LP proof-term vocabulary + ⋀-list algebra ----

   The LP lemma/symbol names the emitter references live here — the only
   place LP-side names appear outside the [Pp_lp] formula printer — together
   with the small ⋀-list proof-term algebra built on them.  Everything
   returns a structured [Lp_tree.term]; nothing renders to a string. *)

let prj k t = L.App (L.Name "prj", [L.Name (string_of_int k); t])

let conj_intro a b = L.App (L.Name "\xe2\x8b\x80_intro", [a; b]) (* ⋀_intro *)
let conj_nil_prf = L.Name "\xe2\x8b\x80_nil_prf"                 (* ⋀_nil_prf *)
let conj_init t = L.App (L.Name "\xe2\x8b\x80_init", [t])        (* ⋀_init *)
let conj_last t = L.App (L.Name "\xe2\x8b\x80_last", [t])        (* ⋀_last *)
let true_intro = L.Name "\xe2\x8a\xa4\xe1\xb5\xa2"             (* ⊤ᵢ *)
let eq_refl t = L.App (L.Name "eq_refl", [t])

(* Build `π (⋀ (∎ ∷ e₀ ∷ … ∷ eₙ₋₁))` from element proofs: a snoc left-fold
   ⋀_intro (… (⋀_intro ⋀_nil_prf e₀) …) eₙ₋₁ bottoming in ⋀_nil_prf.
   ⋀_intro's implicits are inferred from the expected type.  A singleton
   needs no wrapping (⋀ (∎ ∷ e) ≡ e). *)
let conj_chain = function
  | [t] -> t
  | ts -> List.fold_left conj_intro conj_nil_prf ts

(* Extract conjunct [k] of an n-element ⋀-list held by [var]: peel (n-1-k)
   elements off the tail with ⋀_init, then take the last with ⋀_last.
   Element 0 bottoms at ⋀ (∎ ∷ P₀) ≡ P₀, so it needs no ⋀_last. *)
let rec init_chain var j =
  if j = 0 then var else conj_init (init_chain var (j - 1))

let extract var conjs k =
  let n = List.length conjs in
  if k = 0 then init_chain var (n - 1)
  else conj_last (init_chain var (n - 1 - k))

(* AND5: rebuild the ⋀-list with conjunct [j] (an implication) discharged.
   [j]'s antecedent is the conjunct(s) at [ant_positions], combined and
   applied to (extract j); the other conjuncts pass through unchanged. *)
let and5_fwd var conjs ant_positions j =
  let n = List.length conjs in
  let others =
    List.filter (fun k -> k <> j) (List.init n Fun.id)
    |> List.map (fun k -> extract var conjs k)
  in
  let ant_proof =
    conj_chain (List.map (fun i -> extract var conjs i) ant_positions)
  in
  let discharged = L.App (extract var conjs j, [ant_proof]) in
  conj_chain (others @ [discharged])

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

   Each `Hyp_search` rule has a fixed LP-type signature; the hypothesis
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
  | "EAXM1", Binary (Imp, Eq (e, f), _) ->
    (* lp/rules/Eq.lp EAXM1 expects π (¬ (F = E)) — the swap is in the spec *)
    Some (Unary (Not, Eq (f, e)))
  | "EAXM2", Binary (Imp, Unary (Not, Eq (e, f)), _) ->
    Some (Eq (f, e))
  | _ -> None

let find_hyp_by_pred ctx pred =
  List.find_map
    (fun (name, p) -> if p = pred then Some name else None) ctx.hyps

(* AR4 needs an explicit F with `F ≤ 𝟎` provable in scope.  The replay
   doesn't record F, but `F ≤ 𝟎` is one of the hypotheses PP introduced
   on the way to the leaf — find it and return (F, its hyp name). *)
let find_leq_zero_hyp ctx =
  List.find_map
    (fun (name, p) -> match p with
       | Leq (f, Nat 0) -> Some (f, name)
       | _ -> None) ctx.hyps

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
      (L.App (L.Name "\xe2\xa8\xbe", [L.Name "unit"; prj i (L.Name x_name)]), [pp_var])
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
  | Bind (binder, vars, Unary (Not, body)) when binder = Bang || binder = Forall || binder = Forall2 ->
    Some (binder, vars, body)
  | _ -> None

let collect_conj_leaves = Pp_lp.conj_leaves

let leaf_evidence ctx env leaf =
  if is_true_atom leaf then Some true_intro
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
    Some (conj_chain (List.map Option.get opt_evs))
  else None

let find_ins_contradiction ctx =
  let try_candidate (lp_witness, pp_vars) (h_name, h_pred) =
    match ins_hyp_shape h_pred with
    | Some (binder, h_vars, h_body)
      when List.length h_vars = List.length pp_vars ->
      let env = List.map2 (fun v pp -> (v, Var pp)) h_vars pp_vars in
      (match match_conj ctx env h_body with
       | Some conj_ev ->
         let elim_lemma = match binder with
           | Bang -> "!!_to_pi"
           | Forall -> "♢_to_pi"
           | Forall2 -> "♡_to_pi"
           | Exists -> failwith "Exists binder in ins_hyp_shape"
         in
         Some (L.Refine (L.Name elim_lemma,
           [L.Hole; L.Name h_name; lp_witness; conj_ev]))
       | None -> None)
    | _ -> None
  in
  List.find_map (fun x ->
    List.find_map (fun cand ->
      List.find_map (try_candidate cand) ctx.hyps
    ) (witness_candidates x)
  ) ctx.xs

(* Diagnostic for a failed [find_ins_contradiction], built from the same
   predicates the search uses so it reports exactly why no (hyp × witness)
   discharged the contradiction: the hypotheses and witnesses in scope, and
   for each universal hyp the witness leaving the fewest unmatched conjuncts
   together with which conjuncts those are (rendered in PP syntax). *)
let ins_diagnostic ctx =
  let b = Buffer.create 256 in
  let add fmt = Printf.ksprintf (Buffer.add_string b) fmt in
  let hyps = List.rev ctx.hyps and xs = List.rev ctx.xs in
  add "  hypotheses in scope (%d):" (List.length hyps);
  if hyps = [] then add " (none)"
  else List.iter (fun (h, p) -> add "\n    %s : %s" h (Emit_pp.prd_to_pp p)) hyps;
  add "\n  witnesses in scope (%d binder%s):"
    (List.length xs) (if List.length xs = 1 then "" else "s");
  if xs = [] then add " (none — INS reached outside any quantifier binder)"
  else List.iter (fun (x, vs) -> add "\n    %s \xe2\x86\xa6 [%s]" x (String.concat ", " vs)) xs;
  let univ =
    List.filter_map (fun (h, p) ->
      match ins_hyp_shape p with
      | Some (_, vars, body) -> Some (h, vars, body)
      | None -> None) hyps
  in
  (match univ with
   | [] ->
     add "\n  no in-scope hypothesis has the universal form \
          `\xe2\x88\x80x.\xc2\xac(\xe2\x80\xa6)` that INS instantiates"
   | _ ->
     add "\n  universal hyps examined (closest witness per hyp):";
     List.iter (fun (h, vars, body) ->
       let leaves = collect_conj_leaves body in
       let attempts =
         List.concat_map witness_candidates xs
         |> List.filter_map (fun (_w, pp_vars) ->
              if List.length vars <> List.length pp_vars then None
              else
                let env = List.map2 (fun v pp -> (v, Var pp)) vars pp_vars in
                let missing =
                  List.filter
                    (fun l -> not (is_true_atom l) && leaf_evidence ctx env l = None)
                    leaves
                in
                Some (pp_vars, env, missing))
       in
       match
         List.sort (fun (_, _, a) (_, _, c) ->
           compare (List.length a) (List.length c)) attempts
       with
       | [] ->
         add "\n    %s : binds %d var(s); no in-scope witness has that arity"
           h (List.length vars)
       | (pp_vars, env, missing) :: _ ->
         add "\n    %s with witness [%s]: %d/%d conjunct(s) unmatched"
           h (String.concat ", " pp_vars) (List.length missing) (List.length leaves);
         List.iter (fun l ->
           add "\n        \xe2\x9c\x97 %s" (Emit_pp.prd_to_pp (subst_prd env l)))
           missing)
       univ);
  Buffer.contents b
