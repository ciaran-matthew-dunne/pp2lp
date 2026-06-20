(* Per-rule tactic construction.

   Given a rule and its annotation, build the single `refine …` tactic (or
   the hypothesis/witness/value arguments it needs).  Sits above [Emit_ctx]
   (whose context, searches, and ⋀-list algebra it uses) and below
   [Translate] (the walker, which decides tree structure and calls in here
   for each node's tactic). *)

open Syntax_pp
open Emit_ctx

module L = Lp_tree

(* ---- PP-formula rule arguments ----

   Rule arguments carrying a predicate/expression (AR3/AR9/AR10 solver
   results, NRM20/22's substituted E) may mention PP variables bound by an
   enclosing ALL7/ALL8 binder.  In LP those binders introduce a single
   `Tuple n` value, so var k of tuple `x` must render as `prj k x` — exactly
   the env the n-ary quantifier kernel uses.  Build that env from `ctx.xs`
   and carry it on the [Pred]/[Exp] node so [Pp_lp] applies the projections
   when the printer runs.  (With no in-scope binder the env is empty.) *)
let pp_env_of ctx =
  List.concat_map (fun (x_name, pp_vars) ->
    List.mapi (fun i v -> (v, L.Proj (i, x_name))) pp_vars
  ) ctx.xs

let pred_term ctx prd = L.Pred (pp_env_of ctx, prd)
let exp_term ctx e = L.Exp (pp_env_of ctx, e)

(* ---- refine-argument assembly ---- *)

(* Value arguments rendered from the rule's PP-side arg (AR3's exp, AR9's
   pred); env-carried so enclosing-binder vars project correctly. *)
let dynamic_value_args ctx rule arg =
  match Rule_db.emit rule, arg with
  | Rule_db.Ar3, Some (PipeArg (a, _b)) -> [exp_term ctx a]
  | Rule_db.Ar9, Some (ExpArg e) -> [exp_term ctx e]
  | _, _ -> []

(* Proof arguments the LP signature needs *before* the slot holes —
   solver side-conditions the replay doesn't carry (now generated in
   [tactic_for_rule] or failed loud — never `trust`), and the witness/hyp
   pair placeholders. *)
let metadata_extra_args rule =
  match Rule_db.emit rule with
  | Rule_db.Ar9 ->
    (* AR9's real dispatch (in [tactic_for_rule]) supplies the E = F equality as
       `eq_refl` (E ≡ F on every occurrence) and never reaches this generic
       metadata path.  If it ever does, fail rather than emit `trust`. *)
    failwith "rule_emit: AR9 reached the generic metadata path (no F value arg) \
              — refusing to emit trust for the E = F equality"
  | Rule_db.Witness_hyp -> [L.Hole; L.Hole]
  (* Ar4/Ar5_6/Ar7_8 build their own args in [tactic_for_rule] and never
     reach the generic path, so they need no metadata here. *)
  | Rule_db.Default | Rule_db.Trust_cons | Rule_db.Hyp_search | Rule_db.Ins
  | Rule_db.And5 | Rule_db.Opr _ | Rule_db.Axm8 | Rule_db.Nrm20 | Rule_db.Nrm21 | Rule_db.Nrm22 | Rule_db.Nrm23
  | Rule_db.Nrm26 | Rule_db.Nrm2730 | Rule_db.Eqs2 | Rule_db.Eimp5 | Rule_db.Ectr | Rule_db.Arith
  | Rule_db.Egalite
  | Rule_db.Ar2
  | Rule_db.Ar3 | Rule_db.Ar3_f | Rule_db.Ar4 | Rule_db.Ar5_6 | Rule_db.Ar7_8 | Rule_db.Ar10
  | Rule_db.Bool_split -> []

(* Holes for the rule's derivation slots.  A Con slot under the [Trust_cons]
   strategy has no generated proof, so it fails loud rather than emit `trust`
   (the historical fallback, removed 2026-06-12). *)
let slot_hole_args rule =
  let trust_cons = Rule_db.emit rule = Rule_db.Trust_cons in
  Rule_db.slots rule
  |> List.map (function
    | Rule_db.Con ->
      if trust_cons then
        failwith (Printf.sprintf
          "rule_emit: %s (Trust_cons) has an unproven Con side-condition \
           — refusing to emit trust" rule)
      else L.Hole
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

(* NRM20/NRM22: recover the substituted expression E from a normalisation
   goal `(♡ (x₁,…), ¬ (… ∧ (x₁ = E) ∧ …)) ⇒ R`.  E is the RHS of the equality
   conjunct whose LHS is the leading binder var (the `prj 0` slot).  Per the
   actual replays — not the spec — PP places this equality at the *head* of the
   conjunction for NRM20 but at the *tail* (after a `⊤` from NRM14) for NRM22,
   so we match it by the bound var rather than by position.  The reversed
   `E = x` orientation belongs to NRM21/23, which no current replay exercises. *)
(* The binder list of a `forall2(…) ⇒ Q` annotation (NRM20/21/26's shape). *)
let forall2_vars_of_goal = function
  | Some (Binary (Imp, Bind (Forall2, vars, _), _)) -> Some vars
  | _ -> None

(* Position (= prj slot, PP binder position i ↦ prj i) and name of the one
   var in [vars] missing from [child_vars] — the binder the rule dropped,
   read off the annotation diff. *)
let dropped_var_pos vars child_vars =
  let rec go i = function
    | [] -> None
    | v :: rest ->
      if List.mem v child_vars then go (i + 1) rest else Some (i, v)
  in
  go 0 vars

(* `((♡v,¬⋀L) ⇒ Q) = ((♡v,¬⋀L') ⇒ Q)` where L' is L with conjunct [j] (of
   [n_cs]) bubbled to the end: an eq_trans chain of conj_swap_last2 steps,
   each lifted by conj_init_cong once per element above it, wrapped in
   not_cong/!!_cong/imp_cong_l.  All implicits are inferred from the goal
   term at check time, so the chain is built bare. *)
let conj_bubble_goal_cong ctx n_cs j =
  let rec lift n t =
    if n = 0 then t
    else lift (n - 1) (L.App (L.Name "conj_init_cong", [ t ]))
  in
  let rec chain i =
    let step = lift (n_cs - 2 - i) (L.Name "conj_swap_last2") in
    if i = n_cs - 2 then step
    else L.App (L.Name "eq_trans", [ step; chain (i + 1) ])
  in
  let u = fresh_x_local ctx in
  L.App (L.Name "imp_cong_l",
    [ L.App (L.Name "!!_cong",
        [ L.Lambda (u, None, L.App (L.Name "not_cong", [ chain j ])) ]) ])

(* The orientation-respecting pinning-equality conjunct: its index and the
   witness side.  [rev] = the pinned var on the RHS (NRM21/23). *)
let pin_eq_conjunct ~rev pinned cs =
  let eq_e = function
    | Eq (Var x, e) when (not rev) && x = pinned -> Some e
    | Eq (e, Var x) when rev && x = pinned -> Some e
    | _ -> None
  in
  let rec find j = function
    | [] -> None
    | c :: rest ->
      (match eq_e c with Some e -> Some (j, e) | None -> find (j + 1) rest)
  in
  find 0 cs

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
  let fallback = L.Refine (L.Name rule, default_args) in
  match goal_of_anno anno with
  | None -> fallback
  | Some goal ->
    match expected_hyp_pred rule goal with
    | None -> fallback
    | Some needed ->
      match find_hyp_by_pred ctx needed with
      | Some name ->
        L.Refine (L.Name rule, replace_last default_args (L.Name name))
      | None -> fallback

let tactic_for_witness_hyp ctx rule anno =
  let fallback = L.Refine (L.Name rule, [L.Hole; L.Hole]) in
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
    | Some (witness, h) -> L.Refine (L.Name rule, [witness; L.Name h])
    | None -> fallback

(* The AXM8 extraction function `λ h, conj_prj h k` : π C → π r, where the goal
   is `C ⇒ r` and r is the conjunct at position k of C.  Shared by the base AXM8
   tactic and the chain-form AXM8_1 (which wraps it in `mk_0 ∘ prop_eq_top`).
   [None] when the goal isn't `C ⇒ r` with r a conjunct. *)
let axm8_extraction ctx anno : L.term option =
  match goal_of_anno anno with
  | Some (Binary (Imp, lhs, rhs)) ->
    let conjs = conjuncts lhs in
    (match find_conjunct_pos conjs rhs with
     | Some k ->
       ctx.n <- ctx.n + 1;
       let h = Printf.sprintf "_h%d" ctx.n in
       Some (L.Lambda (h, None, conj_prj_at (L.Name h) conjs k))
     | None -> None)
  | _ -> None

let tactic_for_axm8 ctx rule anno =
  match axm8_extraction ctx anno with
  | Some f -> L.Refine (L.Name rule, [f])
  | None -> L.Refine (L.Name rule, [L.Hole])

(* ECTR1-6: equality-substitution contradiction leaves.  Both premises
   live in PP's store; the conclusion (the annotation's antecedent) gives
   the shape:
     (a = b) ⇒ P — ECTR1/2: ¬(Q E) and Q F in H; the conclusion IS the eq
     ¬G ⇒ Q      — ECTR3/4: E = F (resp. F = E) and P F in H
     G ⇒ Q       — ECTR5/6: E = F (resp. F = E) and ¬(P F) in H
   The direction found selects the lemma.  The substituted side must be a
   variable (PP's set translator builds these over simple variables). *)
let tactic_for_ectr ctx rule anno =
  let fail reason =
    failwith (Printf.sprintf "translate: %s — %s" rule reason)
  in
  let abstract x g =
    let z = fresh_x_local ctx in
    L.Lambda (z, Some L.Tau_i, pred_term ctx (subst_prd [(x, Var z)] g))
  in
  (* ECTR3/4: the rewritten side may be a compound sub-term, so abstract the
     whole expression (not just a variable) out of the goal atom. *)
  let abstract_exp e_from g =
    let z = fresh_x_local ctx in
    L.Lambda (z, Some L.Tau_i,
              pred_term ctx (replace_subexp_prd e_from (Var z) g))
  in
  match goal_of_anno anno with
  | Some (Binary (Imp, Eq (a, b), _)) ->
    (match find_ectr12 ctx a b with
     | Some (x, q, hn, hh, swapped) ->
       L.Refine (L.Name (if swapped then "ECTR2" else "ECTR1"),
                 [abstract x q; L.Name hn; L.Name hh])
     | None ->
       fail "no ¬(Q E) / Q F hyp pair matches the equality antecedent")
  | Some (Binary (Imp, Unary (Not, g), _)) ->
    (match find_ectr34 ctx g with
     | Some (e_from, heq, swapped, hh) ->
       L.Refine (L.Name (if swapped then "ECTR4" else "ECTR3"),
                 [abstract_exp e_from g; L.Name heq; L.Name hh])
     | None ->
       fail "no (equality hyp × substituted hyp) pair matches the negated \
             goal atom")
  | Some (Binary (Imp, g, _)) ->
    (match find_ectr56 ctx g with
     | Some (x, heq, hn, swapped) ->
       L.Refine (L.Name (if swapped then "ECTR6" else "ECTR5"),
                 [abstract x g; L.Name heq; L.Name hn])
     | None ->
       fail "no (equality hyp × negated substituted hyp) pair matches the \
             goal antecedent")
  | _ -> fail "expected an implication annotation"

(* Build the single `refine` tactic for a rule.  Exhaustive over
   [Rule_db.emit]: the walker handles the constructors that expand to
   *tree structure* (And5/Opr/Ins/branching) before reaching here, so
   those fall to the generic-args arm; everything else is dispatched by
   strategy. *)
let tactic_for_rule ctx rule arg anno children =
  match Rule_db.emit rule with
  | Rule_db.Arith ->
    (* ARITH `⊥`-terminal: generated Farkas combination of the ≤-hyps. *)
    (match find_arith_contradiction ctx with
     | Some t -> t
     | None ->
       failwith (Printf.sprintf
         "translate: ARITH — no small Farkas combination of the in-scope \
          `e ≤ 𝟎` hypotheses sums to 𝟏\n%s" (arith_diagnostic ctx)))
  | Rule_db.Ectr when children = [] -> tactic_for_ectr ctx rule anno
  | Rule_db.Hyp_search when children = [] -> tactic_for_hyp ctx rule arg anno
  | Rule_db.Axm8 when children = [] -> tactic_for_axm8 ctx rule anno
  | Rule_db.Witness_hyp -> tactic_for_witness_hyp ctx rule anno
  | Rule_db.Bool_split ->
    (* BOOL31/32/41/42: the `V ϵ BOOL` Con slot.  V is the non-literal side of
       the goal's `¬(V = b)` / `¬(b = V)` (BOOL31/32 vs BOOL41/42).  When V is a
       bound tuple slot, discharge from an injected `Π u, prj k u ϵ BOOL` typing
       premise applied to the in-scope tuple; when PP concretised V to a boolean
       literal, from the `b*_in_bool` axiom.  No source ⇒ fail (never trust). *)
    let no_bool_typing () =
      failwith (Printf.sprintf
        "rule_emit: %s `V ϵ BOOL` side-condition — V has no injected typing \
         premise or boolean literal, refusing to emit trust" rule)
    in
    let con =
      match goal_of_anno anno with
      | Some (Binary (Imp, Unary (Not, Eq (a, b)), _)) ->
        let v_exp =
          match base rule with "BOOL31" | "BOOL32" -> a | _ -> b in
        (match v_exp with
         | Var ("TRUE" | "VRAI") -> L.Name "btrue_in_bool"
         | Var ("FALSE" | "FAUX") -> L.Name "bfalse_in_bool"
         | Var v -> (match bool_typing_term ctx v with
                     | Some t -> t | None -> no_bool_typing ())
         | _ -> no_bool_typing ())
      | _ -> no_bool_typing ()
    in
    L.Refine (L.Name rule, [con; L.Hole])
  | Rule_db.Eimp5 ->
    (* EIMP51 [E F] : π (¬ (F = E)) → π P → π (¬ (E = F) ⇒ P)
       EIMP52 [E F] : π (F = E)     → π P → π ((E = F) ⇒ P)
       PP discharges the implication using the *swapped-orientation* equality
       already in its store (introduced by the enclosing IMP4 / assumed): the
       goal carries `E = F`, the hyp carries `F = E`.  Supply that hyp as the
       explicit first argument; the Seq child proves P.  Fail loud (never
       trust) if the swapped equality is not in scope. *)
    let ev =
      match base rule, goal_of_anno anno with
      | "EIMP51", Some (Binary (Imp, Unary (Not, Eq (e, f)), _)) ->
        find_hyp_by_pred ctx (Unary (Not, Eq (f, e)))
      | "EIMP52", Some (Binary (Imp, Eq (e, f), _)) ->
        find_hyp_by_pred ctx (Eq (f, e))
      | _ -> None
    in
    (match ev with
     | Some h -> L.Refine (L.Name (base rule), [L.Name h; L.Hole])
     | None ->
       failwith (Printf.sprintf
         "rule_emit: %s — the swapped-orientation equality (the hyp PP commutes \
          the goal's equality against) is not in scope, refusing to emit trust"
         (base rule)))
  | Rule_db.Ar10 ->
    (* AR10 [P Q R] : π (P = Q) → π (Q ⇒ R) → π (P ⇒ R).  PP's `solveur(P) = Q`
       is the identity on every corpus occurrence (P ≡ Q — the antecedent equals
       its own normal form), so the equality is `eq_refl` and Q is *inferred* from
       the goal `P ⇒ R` (which is `Q ⇒ R` since P ≡ Q): `refine AR10 (eq_refl _) _`.
       The old form spelled Q out twice (explicit arg + `eq_refl Q`), which
       dominated AR10's emitted size across tens of thousands of sites. *)
    L.Refine (L.Name "AR10", [L.App (L.Name "eq_refl", [L.Hole]); L.Hole])
  | Rule_db.Nrm20 | Rule_db.Nrm21 ->
    (* Drop a binder pinned by an `x = E` (NRM20) / `E = x` (NRM21) conjunct.
       PP may pin *any* binder at *any* slot k, with E mentioning the other
       still-bound vars (`#x.#y.(x = y)` pins x at y).  One generic lemma covers
       every slot: emit the slot k and E as a function of the remaining tuple
       (the pinned var removed, the rest projected in `rvars` order: index i ↦
       `prj i w` — removing slot k makes each remaining binder land at its own
       index).  The pinning equality must be the conjunct list's tail, so bubble
       it there first (generated swap-congruence) when it isn't.  The pinned var
       is read off the annotation diff against the child's binder list (fallback:
       the first orientation-matching equality whose var is in-block). *)
    let rev = Rule_db.emit rule = Rule_db.Nrm21 in
    let rule_name = if rev then "NRM21" else "NRM20" in
    (match goal_of_anno anno with
     | Some (Binary (Imp, Bind (Forall2, vars, Unary (Not, body)), _)) ->
       let cs = conjuncts body in
       let n_cs = List.length cs in
       let pos_of v =
         let rec go i = function
           | [] -> None
           | x :: rest -> if x = v then Some i else go (i + 1) rest
         in go 0 vars
       in
       let pinned_opt =
         match children with
         | [c] ->
           (match forall2_vars_of_goal (goal_of_anno (Proof_tree.anno_of c)) with
            | Some cvars when List.length cvars = List.length vars - 1 ->
              Option.map snd (dropped_var_pos vars cvars)
            | _ -> None)
         | _ -> None
       in
       let candidate =
         let try_pinned p =
           Option.map (fun (j, e) -> (p, j, e)) (pin_eq_conjunct ~rev p cs)
         in
         match pinned_opt with
         | Some p -> try_pinned p
         | None -> List.find_map try_pinned vars
       in
       (match candidate with
        | Some (pinned, j, e) ->
          let k = Option.get (pos_of pinned) in
          let e_vars =
            (Free_vars.free_vars_of_prd (Eq (e, Lit "0"))).Free_vars.exp_vars in
          let head_ok =
            (not rev) && j = 0 && k = 0 && n_cs > 1
            && not (List.exists (fun v -> Free_vars.SS.mem v e_vars) vars)
          in
          if head_ok then
            (* Fast path for the dominant shape (all of prv): slot-0 head equality
               with block-closed E.  NRM20H peels the head equality with popl/dropl
               — no rotation, the per-site cost that otherwise pushes NRM20-dense
               proofs over the check budget.  Semantically the slot-0 head case of
               the general NRM20 below. *)
            let env = pp_env_of ctx in
            let v = fresh_x_local ctx in
            let heq_eq = L.Eq (prj 0 (L.Name v), L.Exp (env, e)) in
            L.Refine (L.Name "NRM20H",
              [ L.Exp (env, e);
                L.Lambda (v, None, eq_refl heq_eq);
                L.Hole ])
          else begin
            (* General: `ins`/`rm` at slot k; E is a function of the remaining tuple
               (the pinned var removed, the rest projected in `rvars` order —
               removing slot k makes each remaining binder land at its own index).
               The pinning equality must be the conjunct-list tail, so bubble it
               there (generated swap-congruence) when it isn't already. *)
            let rvars = List.filter (fun v -> v <> pinned) vars in
            let w = fresh_x_local ctx in
            let env' =
              List.mapi (fun i v -> (v, L.Proj (i, w))) rvars @ pp_env_of ctx in
            let args =
              [ L.Name (string_of_int k);
                L.Lambda (w, None, L.Exp (env', e)); L.Hole ] in
            if j = n_cs - 1 then L.Refine (L.Name rule_name, args)
            else
              L.Refine (L.Name "=⇒",
                [ L.App (L.Name "eq_sym", [ conj_bubble_goal_cong ctx n_cs j ]);
                  L.App (L.Name rule_name, args) ])
          end
        | None ->
          failwith (Printf.sprintf
            "translate: %s annotation lacks an `%s` equality conjunct \
             for the dropped binder"
            rule_name (if rev then "E = x" else "x = E")))
     | _ ->
       failwith (Printf.sprintf
         "translate: %s expected a `forall2(…)·¬(…) ⇒ Q` annotation" rule_name))
  | Rule_db.Nrm26 ->
    (* Drop an unused binder at the slot PP names; one generic lemma, the emitter
       supplies k (annotation diff against the child's binder list).  Without a
       usable child annotation, default to the last-listed binder (slot |vars|-1)
       — the position the historical tuple_prepend form dropped. *)
    let emit k = L.Refine (L.Name "NRM26", [L.Name (string_of_int k); L.Hole]) in
    (match forall2_vars_of_goal (goal_of_anno anno) with
     | Some vars ->
       let default_k = List.length vars - 1 in
       let k =
         match children with
         | [c] ->
           (match forall2_vars_of_goal (goal_of_anno (Proof_tree.anno_of c)) with
            | Some cvars when List.length cvars = List.length vars - 1 ->
              (match dropped_var_pos vars cvars with
               | Some (k, _) -> k | None -> default_k)
            | _ -> default_k)
         | _ -> default_k
       in emit k
     | None -> emit 0)
  | Rule_db.Nrm22 | Rule_db.Nrm23 ->
    (* Single-binder pins.  NRM22 [ps] [Q] (E) concludes
       `(♡ v : Tuple 1, ¬ ⋀ (ps v ∷ (prj 0 v = E))) ⇒ Q` (NRM23G the
       reversed `E = prj 0 v`); E may mention enclosing binders, so
       env-carry it.  Like NRM20/21, the pinning equality may sit anywhere
       in the conjunct list — bubble it to the tail first when needed. *)
    let rev = Rule_db.emit rule = Rule_db.Nrm23 in
    let rule_name = if rev then "NRM23G" else "NRM22" in
    (match goal_of_anno anno with
     | Some (Binary (Imp, Bind (Forall2, [ v0 ], Unary (Not, body)), _)) ->
       let cs = conjuncts body in
       let n_cs = List.length cs in
       (match pin_eq_conjunct ~rev v0 cs with
        | Some (j, e) ->
          let plain = L.App (L.Name rule_name, [ exp_term ctx e; L.Hole ]) in
          if j = n_cs - 1 then L.Refine (L.Name rule_name, [ exp_term ctx e; L.Hole ])
          else
            L.Refine (L.Name "=⇒",
              [ L.App (L.Name "eq_sym", [ conj_bubble_goal_cong ctx n_cs j ]);
                plain ])
        | None ->
          failwith (Printf.sprintf
            "translate: %s annotation lacks an `%s` equality conjunct \
             pinning the binder"
            rule_name (if rev then "E = x" else "x = E")))
     | _ ->
       failwith (Printf.sprintf
         "translate: %s expected a 1-binder `forall2(x)·¬(…) ⇒ Q` annotation"
         rule_name))
  | Rule_db.Ar2 ->
    (* AR2 leaf: `(leq (from_int a) (from_int b)) ⇒ R`, PP's solver having found
       a > b for concrete ℤ literals a, b (it comes out of AR3's `1−a`, e.g. 2 ≤ 0).
       a, b, R are implicit on the `AR2` lemma: `from_int` is injective, so unifying
       the goal's `from_int a` / `from_int b` solves them; `Stdlib.Z.> a b` then
       computes to `¬¬⊤`, so the proof is just `λ k, k ⊤ᵢ`.  Still guard the goal
       shape: fail loud (never trust) if the comparison isn't between concrete
       literals; if a ≤ b (PP mis-emitted) the `λ k, k ⊤ᵢ` won't type-check — loud. *)
    (match goal_of_anno anno with
     | Some (Binary (Imp, Leq (Lit _, Lit _), _)) ->
       L.Refine (L.Name rule,
         [ L.Lambda ("k", None,
             L.App (L.Name "k", [ L.Name "\xe2\x8a\xa4\xe1\xb5\xa2" (* ⊤ᵢ *) ])) ])
     | _ ->
       failwith "rule_emit: AR2 — expected a concrete ℤ-literal comparison \
                 `(a ≤ b) ⇒ R` (a, b literals); refusing to emit trust")
  | Rule_db.Ar5_6 ->
    (* AR5 [a R] : π (a ≪ 𝟎) → … → π ((—a ≤ 𝟎) ⇒ R) — the antisymmetry-to-zero:
       given the antecedent `—a ≤ 𝟎`, the missing bound `a ≤ 𝟎` makes a = 𝟎.
       AR6 is the mirror (antecedent `a ≤ 𝟎`, bound `—a ≤ 𝟎`).  That bound is
       PP's solver fact, but it's the matching `≤ 𝟎` hypothesis in scope — find
       it; fail loud if absent (never trust).  The Seq slot is the continuation
       child.  The leading `hai : π (a ϵ INT)` lets `leq_antisym` recover `a = 𝟎`. *)
    let a_and_bound =
      match base rule, goal_of_anno anno with
      | "AR5", Some (Binary (Imp, Leq (Neg a, Lit "0"), _)) -> Some (a, Leq (a, Lit "0"))
      | "AR6", Some (Binary (Imp, Leq (a, Lit "0"), _)) -> Some (a, Leq (Neg a, Lit "0"))
      | _ -> None
    in
    let con, hai =
      match a_and_bound with
      | Some (a, bound) ->
        (match find_hyp_by_pred ctx bound with
         | Some h -> L.Name h, Arith_proofs.int_evidence (proj_env_of_ctx ctx) a
         | None -> failwith "rule_emit: AR5/AR6 — the matching `≤ 𝟎` bound \
                             hypothesis is not in scope, refusing to emit trust")
      | None -> failwith "rule_emit: AR5/AR6 — unexpected goal shape (no `±a ≤ 𝟎` \
                          antecedent), refusing to emit trust"
    in
    L.Refine (L.Name rule, [hai; con; L.Hole])
  | Rule_db.Ar4 ->
    (* AR4 [E R] (F) : π (F ≤ 𝟎) → π ((E + F) > 𝟎) → π ((E ≤ 𝟎) ⇒ R).  A leaf
       deriving ⊥ from a hyp `F ≤ 𝟎` and `(E + F) > 𝟎`.  AR4 follows AR3's
       `𝟏 − a` normalisation, so E = `𝟏 − F` for the cancelling hyp F and
       `E + F = 𝟏`; then `(E+F) > 𝟎 = ¬((E+F) ≤ 𝟎)` is `one_not_leq_zero`
       transported along the generated `(E+F) = 𝟏` — no trust.  Pick the F≤𝟎 hyp
       that cancels; fail loud if none does (never trust). *)
    let env = proj_env_of_ctx ctx in
    let e_opt = match goal_of_anno anno with
      | Some (Binary (Imp, Leq (e, Lit "0"), _)) -> Some e | _ -> None in
    let generated =
      match e_opt with
      | Some e ->
        List.find_map (fun (name, p) -> match p with
          | Leq (f, Lit "0") ->
            Option.map (fun h_gt ->
              (* E, F implicit: F from the `name : F ≤ 𝟎` hyp, E from the goal,
                 both via the B.lp `to_int`/`isGt` unification rules.  `(E+F) > 𝟎`
                 is the reflective [prove_gt_zero] term. *)
              L.Refine (L.Name rule, [L.Name name; h_gt]))
              (Arith_proofs.prove_gt_zero env (AOp (Add, e, f)))
          | _ -> None) ctx.hyps
      | None -> None
    in
    (match generated with
     | Some t -> t
     | None ->
       match find_leq_zero_hyp ctx with
       | Some _ ->
         failwith "rule_emit: AR4 — an `F ≤ 𝟎` hyp is in scope but its \
                   `(E+F) > 𝟎` proof didn't generate (prove_gt_zero failed), \
                   refusing to emit trust"
       | None ->
         failwith "rule_emit: AR4 needs an in-scope `F ≤ 𝟎` hypothesis, none found \
                   (the solver's F is not recorded in the replay)")
  | Rule_db.Ar7_8 ->
    (* AR7/AR8 need the solver's witness (the `a` in `a + c = 𝟎`), which PP
       does not record in the replay (see doc Known-broken).  Fail explicitly
       rather than emit an ill-typed `refine`. *)
    failwith "translate: AR7/AR8 unsupported — the solver witness (a in a + c = 𝟎) \
              is not recorded in the replay"
  | Rule_db.Ar9 ->
    (* AR9 (F) : π (E = F) → π ((F ≤ 𝟎) ⇒ R) → π ((E ≤ 𝟎) ⇒ R).  PP's `solveur(E) = F`;
       the `E = F` equality is proved reflectively ([prove_sum_eq]) — `eq_refl` when
       E ≡ F (the corpus norm), the reflective normaliser when F merely reorders E.
       The Seq slot (continuation) is the remaining hole.  Falls back to the bare
       `eq_refl F` when the goal/arg isn't the expected `(E ≤ 𝟎) ⇒ R` with a
       lifted-expression arg (never `trust`). *)
    let reflective =
      match goal_of_anno anno, arg with
      | Some (Binary (Imp, Leq (e_exp, Lit "0"), _)), Some (ExpArg f_exp) ->
        Option.map
          (fun eqpf -> L.Refine (L.Name "AR9", [exp_term ctx f_exp; eqpf; L.Hole]))
          (Arith_proofs.prove_sum_eq (pp_env_of ctx) e_exp f_exp)
      | _ -> None
    in
    (match reflective with
     | Some t -> t
     | None ->
       match dynamic_value_args ctx rule arg with
       | [f] -> L.Refine (L.Name "AR9", [f; L.App (L.Name "eq_refl", [f]); L.Hole])
       | _ -> L.Refine (L.Name rule, default_rule_args ctx rule arg))
  | Rule_db.Hyp_search | Rule_db.Axm8 | Rule_db.Ectr  (* children <> [] — leaf rules, so unreached *)
  | Rule_db.Default | Rule_db.Trust_cons | Rule_db.Ar3 | Rule_db.Ar3_f
  | Rule_db.Nrm2730   (* expands to tree structure in [Translate.default] *)
  | Rule_db.Eqs2      (* handled in [Translate.tree_dispatch] (needs child access) *)
  | Rule_db.Egalite   (* handled in [Translate.tree_dispatch] (needs child access) *)
  | Rule_db.And5 | Rule_db.Opr _ | Rule_db.Ins ->
    (* And5/Opr/Ins expand to tree structure in the walker and never reach
       here as a plain tactic; the rest take generic slot args. *)
    L.Refine (L.Name rule, default_rule_args ctx rule arg)

(* Provenance for the node's primary tactic: rule + replay line + the
   goal PP saw (its annotation), rendered as PP surface syntax. *)
let prov_of rule src_line anno =
  let goal = match anno with
    | Some r -> Emit_pp.prd_to_pp (prd_of_rhs r)
    | None -> "?"
  in
  { L.rule = rule; L.replay_line = src_line; L.goal = goal }
