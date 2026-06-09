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
    List.mapi (fun i v -> (v, (i, x_name))) pp_vars
  ) ctx.xs

let pred_term ctx prd = L.Pred (pp_env_of ctx, prd)
let exp_term ctx e = L.Exp (pp_env_of ctx, e)

(* ---- refine-argument assembly ---- *)

(* Value arguments rendered from the rule's PP-side arg (AR3's exp, AR9's
   pred); env-carried so enclosing-binder vars project correctly. *)
let dynamic_value_args ctx rule arg =
  match Rule_db.emit rule, arg with
  | Rule_db.Ar3, Some (PipeArg (a, _b)) -> [exp_term ctx a]
  | Rule_db.Ar9, Some (Pred p) -> [pred_term ctx p]
  | _, _ -> []

(* Proof arguments the LP signature needs *before* the slot holes —
   solver side-conditions the replay doesn't carry, supplied as `trust`,
   and the witness/hyp pair placeholders. *)
let metadata_extra_args rule =
  match Rule_db.emit rule with
  | Rule_db.Ar9 ->
    (* AR9 (F) : π (E = F) → π ((F ≤ 𝟎) ⇒ R) → π ((E ≤ 𝟎) ⇒ R).
       After the F expression (a dynamic value arg) comes the solver-confirmed
       equality E = F — supply `trust` for it; the Seq slot (the F ≤ 𝟎 ⇒ R
       continuation) is the remaining hole. *)
    [L.Trust]
  | Rule_db.Witness_hyp -> [L.Hole; L.Hole]
  (* Ar4/Ar5_6/Ar7_8 build their own args in [tactic_for_rule] and never
     reach the generic path, so they need no metadata here. *)
  | Rule_db.Default | Rule_db.Trust_cons | Rule_db.Hyp_search | Rule_db.Ins
  | Rule_db.And5 | Rule_db.Opr _ | Rule_db.Axm8 | Rule_db.Nrm20 | Rule_db.Nrm21 | Rule_db.Nrm22 | Rule_db.Nrm23
  | Rule_db.Nrm2730 | Rule_db.Eqs2 | Rule_db.Ectr
  | Rule_db.Ar3 | Rule_db.Ar3_f | Rule_db.Ar4 | Rule_db.Ar5_6 | Rule_db.Ar7_8 | Rule_db.Ar10 -> []

(* Holes for the rule's derivation slots; Con slots become `trust` for
   the [Trust_cons] strategy (solver-confirmed side conditions). *)
let slot_hole_args rule =
  let trust_cons = Rule_db.emit rule = Rule_db.Trust_cons in
  Rule_db.slots rule
  |> List.map (function
    | Rule_db.Con -> if trust_cons then L.Trust else L.Hole
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
let subst_eq_e = function
  | Binary (Imp, Bind (Forall2, v0 :: _, Unary (Not, body)), _) ->
    List.find_map (function
      | Eq (Var lead, e) when lead = v0 -> Some e
      | _ -> None) (conjuncts body)
  | _ -> None

let subst_eq_e_rev = function
  | Binary (Imp, Bind (Forall2, v0 :: _, Unary (Not, body)), _) ->
    List.find_map (function
      | Eq (e, Var lead) when lead = v0 -> Some e
      | _ -> None) (conjuncts body)
  | _ -> None

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

let tactic_for_axm8 ctx rule anno =
  let fallback = L.Refine (L.Name rule, [L.Hole]) in
  match goal_of_anno anno with
  | Some (Binary (Imp, lhs, rhs)) ->
    let conjs = conjuncts lhs in
    (match find_conjunct_pos conjs rhs with
     | Some k ->
       ctx.n <- ctx.n + 1;
       let h = Printf.sprintf "_h%d" ctx.n in
       L.Refine (L.Name rule, [L.Lambda (h, None, extract (L.Name h) conjs k)])
     | None -> fallback)
  | _ -> fallback

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
     | Some (x, heq, swapped, hh) ->
       L.Refine (L.Name (if swapped then "ECTR4" else "ECTR3"),
                 [abstract x g; L.Name heq; L.Name hh])
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
  | Rule_db.Ectr when children = [] -> tactic_for_ectr ctx rule anno
  | Rule_db.Hyp_search when children = [] -> tactic_for_hyp ctx rule arg anno
  | Rule_db.Axm8 when children = [] -> tactic_for_axm8 ctx rule anno
  | Rule_db.Witness_hyp -> tactic_for_witness_hyp ctx rule anno
  | Rule_db.Ar10 ->
    (* AR10 [P Q R] : π (P = Q) → π (Q ⇒ R) → π (P ⇒ R).
       Supply Q explicitly so Lambdapi can type the `trust` equality.
       Q may mention enclosing-binder vars, so carry the tuple-projection
       env rather than the raw PP names. *)
    (match arg with
     | Some (Pred q) ->
       L.Refine (L.Expl (L.Name "AR10"),
         [L.Hole; pred_term ctx q; L.Hole; L.Trust; L.Hole])
     | _ -> L.Refine (L.Name rule, [L.Trust; L.Hole]))
  | Rule_db.Nrm20 ->
    (* NRM20 [n] [ps] [Q] (E) : (Π v, π (popl (ps v) = (prj 0 v = E)))
                              → π (small ⇒ Q) → π (big ⇒ Q).
       `ps` (the full conjunct list) is inferred by unification from the
       goal.  Supply E — the substituted expression, env-carried as it may
       mention enclosing ALL7/ALL8 binders — and the head-equality witness:
       for a concrete `ps`, `popl (ps v)` reduces to `prj 0 v = E`, so
       `eq_refl` discharges it.  The trailing hole is the
       `(♡ y, ¬ ⋀ dropl …) ⇒ Q` continuation child. *)
    (match goal_of_anno anno with
     | Some goal ->
       (match subst_eq_e goal with
        | Some e ->
          let env = pp_env_of ctx in
          let v = fresh_x_local ctx in
          L.Refine (L.Name "NRM20",
            [ L.Exp (env, e);
              L.Lambda (v, None,
                eq_refl (L.Eq (prj 0 (L.Name v), L.Exp (env, e))));
              L.Hole ])
        | None ->
          failwith "translate: NRM20 annotation lacks an `x = E` equality \
                    conjunct (LHS = the leading forall2 binder var)")
     | None -> failwith "translate: NRM20 has no goal annotation")
  | Rule_db.Nrm21 ->
    (* NRM21 [n] [ps] [Q] (E) : (Π v, π (popl (ps v) = (E = prj 0 v)))
                              → π (small ⇒ Q) → π (big ⇒ Q). *)
    (match goal_of_anno anno with
     | Some goal ->
        (match subst_eq_e_rev goal with
         | Some e ->
           let env = pp_env_of ctx in
           let v = fresh_x_local ctx in
           L.Refine (L.Name "NRM21",
             [ L.Exp (env, e);
               L.Lambda (v, None,
                 eq_refl (L.Eq (L.Exp (env, e), prj 0 (L.Name v))));
               L.Hole ])
         | None ->
           failwith "translate: NRM21 annotation lacks an `E = x` equality \
                     conjunct (LHS = the leading forall2 binder var)")
     | None -> failwith "translate: NRM21 has no goal annotation")
  | Rule_db.Nrm22 ->
    (* NRM22 [P] [Q] (E) : π (¬ (P E) ⇒ Q) → π ((♡ v : Tuple 1, ¬ ⋀ (∎ ∷ P
       (prj 0 v) ∷ (prj 0 v = E))) ⇒ Q).  The replay shape (NRM14 feeds it a
       ⊤-headed body) matches this with `P := λ_, ⊤`; the encoding is sound,
       only E must be supplied — Lambdapi infers it nowhere else.  Like NRM20,
       E may mention enclosing binders, so env-carry it.  The trailing hole is
       the `¬ (P E) ⇒ Q` continuation child. *)
    (match goal_of_anno anno with
     | Some goal ->
       (match subst_eq_e goal with
        | Some e -> L.Refine (L.Name "NRM22", [exp_term ctx e; L.Hole])
        | None ->
          failwith "translate: NRM22 annotation lacks an `x = E` equality \
                    conjunct (LHS = the leading forall2 binder var)")
     | None -> failwith "translate: NRM22 has no goal annotation")
  | Rule_db.Nrm23 ->
    (* NRM23 [P] [Q] (E) : π (¬ (P E) ⇒ Q) → π ((♡ v : Tuple 1, ¬ ⋀ (∎ ∷ P
       (prj 0 v) ∷ (E = prj 0 v))) ⇒ Q). *)
    (match goal_of_anno anno with
     | Some goal ->
        (match subst_eq_e_rev goal with
         | Some e -> L.Refine (L.Name "NRM23", [exp_term ctx e; L.Hole])
         | None ->
           failwith "translate: NRM23 annotation lacks an `E = x` equality \
                     conjunct (LHS = the leading forall2 binder var)")
     | None -> failwith "translate: NRM23 has no goal annotation")
  | Rule_db.Ar5_6 ->
    (* AR5/AR6 [a R] : π (solver-fact) → π (cont) → π ((±a ≤ 𝟎) ⇒ R).  `a` is
       implicit (inferred from the goal); the first premise (a ≪ 𝟎 / —a ≤ 𝟎)
       is solver-confirmed → trust.  The Seq slot is the continuation child. *)
    L.Refine (L.Name rule, [L.Trust; L.Hole])
  | Rule_db.Ar4 ->
    (* AR4 [E R] (F) : π (F ≤ 𝟎) → π ((E + F) > 𝟎) → π ((E ≤ 𝟎) ⇒ R).  A leaf
       deriving ⊥ from a hyp `F ≤ 𝟎` and the solver fact `(E + F) > 𝟎`.  F is
       not in the replay; recover it as the LHS of an in-scope `? ≤ 𝟎` hyp,
       then trust the (E+F)>0 conjunct (the documented AR solver gap). *)
    (match find_leq_zero_hyp ctx with
     | Some (f, h) -> L.Refine (L.Name rule, [exp_term ctx f; L.Name h; L.Trust])
     | None ->
       failwith "translate: AR4 needs an in-scope `F ≤ 𝟎` hypothesis, none found \
                 (the solver's F is not recorded in the replay)")
  | Rule_db.Ar7_8 ->
    (* AR7/AR8 need the solver's witness (the `a` in `a + c = 𝟎`), which PP
       does not record in the replay (see doc Known-broken).  Fail explicitly
       rather than emit an ill-typed `refine`. *)
    failwith "translate: AR7/AR8 unsupported — the solver witness (a in a + c = 𝟎) \
              is not recorded in the replay"
  | Rule_db.Hyp_search | Rule_db.Axm8 | Rule_db.Ectr  (* children <> [] — leaf rules, so unreached *)
  | Rule_db.Default | Rule_db.Trust_cons | Rule_db.Ar3 | Rule_db.Ar3_f | Rule_db.Ar9
  | Rule_db.Nrm2730   (* expands to tree structure in [Translate.default] *)
  | Rule_db.Eqs2      (* handled in [Translate.tree_dispatch] (needs child access) *)
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
