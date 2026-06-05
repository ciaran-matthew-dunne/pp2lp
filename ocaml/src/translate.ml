(* The proof-tree walker: turn a [Proof_tree.pp_tree] into an [Lp_tree.t]
   tactic script.  Decides each node's *tree structure* (sequence, assume,
   branch) and asks [Rule_emit] for the node's `refine` tactic; the searches
   and ⋀-list algebra it needs live in [Emit_ctx].

   Two mutually-recursive walks: [tree] for the main sequent proof, and
   [chain_tree] for a Res-typed equality chain (the result-chain child of a
   branching ALL7/XST8).  They mirror each other but differ in the rule
   forms emitted (plain vs primed `_1`) and the slot args assembled. *)

open Syntax_pp

module P = Proof_tree
module L = Lp_tree

open Emit_ctx
open Rule_emit

(* Binder vars introduced by a branching quantifier, read from its goal
   annotation: ALL7's goal is `(binder) ⇒ R`, XST8's is the bare binder.
   Shared by the main-tree [branching] and the Res-chain branch case. *)
let branch_binder_vars rule goal =
  match base rule, goal with
  | "ALL7", Some (Binary (Imp, b, _)) -> Option.value ~default:[] (binder_vars_of b)
  | "XST8", Some g -> Option.value ~default:[] (binder_vars_of g)
  | _ -> []

(* AR3_F congruence-path builder.  PP's forward normalisation rewrites a
   `¬(a ≤ 𝟎)` occurrence to `r ≤ 𝟎` *in place*, wherever it sits in the
   binder-nested goal.  Build the propositional-equality proof `goal = goal'`
   for that exact position by recursing down to the occurrence, composing one
   congruence lemma per connective on the path (`imp_cong_l/r`, `not_cong`,
   `conj_snoc_last_cong`, `!!_cong` under a binder), terminating in `ar3f_eq`;
   the caller transports the live goal with `=⇒`.  `env` renders binder-bound
   vars as `prj k v` — compound NRM8/9 binders included, via the
   `prj`-through-`take`/`drop` rules in Quant.lp.  None when the occurrence
   isn't found on a supported path (caller then falls back to a no-op). *)
let rec ar3f_cong ctx env prd a_exp r_exp : L.term option =
  match prd with
  | Unary (Not, Leq (a', Nat 0)) when a' = a_exp ->
    Option.map
      (fun eqpf -> L.App (L.Name "ar3f_eq",
        [ L.Exp (env, a_exp); L.Exp (env, r_exp); eqpf ]))
      (prove_sum_eq env (AOp (Sub, Nat 1, a_exp)) r_exp)
  | Unary (Not, p) ->
    Option.map (fun c -> L.App (L.Name "not_cong", [c]))
      (ar3f_cong ctx env p a_exp r_exp)
  | Binary (Imp, p, q) ->
    (match ar3f_cong ctx env p a_exp r_exp with
     | Some c -> Some (L.App (L.Name "imp_cong_l", [c]))
     | None ->
       Option.map (fun c -> L.App (L.Name "imp_cong_r", [c]))
         (ar3f_cong ctx env q a_exp r_exp))
  | Binary (And, _, last) ->
    Option.map (fun c -> L.App (L.Name "conj_snoc_last_cong", [c]))
      (ar3f_cong ctx env last a_exp r_exp)
  | Bind (_, vars, body) ->
    let v = fresh_x_local ctx in
    let env' = List.mapi (fun k var -> (var, (k, v))) vars @ env in
    Option.map (fun c -> L.App (L.Name "!!_cong", [L.Lambda (v, None, c)]))
      (ar3f_cong ctx env' body a_exp r_exp)
  | _ -> None

let rec tree ctx node =
  match node with
  | P.Apply { rule; children = [c]; _ }
    when Rule_db.is_hoas_identity (base rule) ->
    (* HOAS identity: no tactic of its own; the child carries provenance. *)
    tree ctx c
  | P.Apply { rule; src_line; anno; _ } ->
    L.Commented (prov_of rule src_line anno, tree_dispatch ctx node)

and tree_dispatch ctx = function
  | P.Apply { rule; anno; children = [c]; _ }
    when Rule_db.emit rule = Rule_db.And5 ->
    (match goal_of_anno anno with
     | Some (Binary (Imp, lhs, _)) ->
       let conjs = Pp_lp.conj_children_left lhs in
       (match find_and5_pair conjs with
        | Some (ant_positions, j) ->
          ctx.n <- ctx.n + 1;
          let h = Printf.sprintf "_h%d" ctx.n in
          let fwd = L.Lambda (h, None, and5_fwd (L.Name h) conjs ant_positions j) in
          L.Then (L.Refine (L.Name "AND5", [fwd; L.Hole]), tree ctx c)
        | None -> default ctx rule None anno [c])
     | _ -> default ctx rule None anno [c])
  | P.Apply { rule; arg; anno; _ }
    when Rule_db.emit rule = Rule_db.Witness_hyp ->
    (* AXM9 (leaf) and NRM19 both discharge directly via the witness/hyp
       pair.  NRM19's child is a placeholder (VR4 / ⊤) with no premise to
       thread, so drop any children. *)
    L.Step (tactic_for_rule ctx rule arg anno [])
  | P.Apply { rule; anno; children = [_]; _ }
    when Rule_db.emit rule = Rule_db.Ins ->
    (match find_ins_contradiction ctx with
     | Some tactic -> L.Step tactic
     | None ->
       let goal = match goal_of_anno anno with
         | Some g -> Emit_pp.prd_to_pp g
         | None -> "(no annotation)"
       in
       failwith (Printf.sprintf
         "INS contradiction search failed — no (universal hyp \xc3\x97 witness) \
          discharges every conjunct\n  goal: %s\n%s"
         goal (ins_diagnostic ctx)))
  | P.Apply { rule; anno; children = [c0; c1]; _ }
    when Rule_db.is_branching (base rule) ->
    branching ctx rule anno c0 c1
  | P.Apply { rule; arg; anno; children; _ } ->
    default ctx rule arg anno children

and default ctx rule arg anno children =
  let goal = goal_of_anno anno in
  match children, Rule_db.emit rule with
  | [c], Rule_db.Opr rtl ->
    (* OPR1: (x = E) ⇒ P x — assume the equality and rewrite x ↦ E.
       OPR2 (rtl=true): (E = x) ⇒ P x — same but rewrite right-to-left. *)
    let eq_pred =
      match goal with
      | Some (Binary (Imp, eq, _)) -> eq
      | _ -> failwith (Printf.sprintf
          "translate: %s expected an implication annotation (got non-⇒ goal)" rule)
    in
    let h = fresh_h ctx eq_pred in
    L.Assume (h,
      L.Then (L.Rewrite { try_ = true; rtl; name = h }, tree ctx c))
  | [c], Rule_db.Ar3 ->
    (* Main-tree AR3.  PP's solver records the sub-premise `𝟏 - a` in a
       neg-normalised order `r` (the PipeArg's 2nd component); the plain AR3
       types its continuation at the literal `𝟏 - a`, so the introduced
       hypothesis ends up shaped `𝟏 - a` while later steps (INS) expect `r`.
       Emit the bridged AR3' with a *generated* `𝟏 - a = r` proof; the child
       continuation then introduces the hyp shaped `r`.  Fall back to plain AR3
       when the shape is unexpected or the equality can't be built. *)
    let env = proj_env_of_ctx ctx in
    let bridged =
      match goal, arg with
      | Some (Binary (Imp, Unary (Not, Leq (a_exp, Nat 0)), _)), Some (PipeArg (_, r_exp)) ->
        Option.map
          (fun eqpf ->
            L.Refine (L.Name "AR3'",
              [L.Exp (env, a_exp); L.Exp (env, r_exp); eqpf; L.Hole]))
          (prove_sum_eq env (AOp (Sub, Nat 1, a_exp)) r_exp)
      | _ -> None
    in
    let tactic =
      match bridged with
      | Some t -> t
      | None -> tactic_for_rule ctx rule arg anno children
    in
    L.Then (tactic, tree ctx c)
  | [c], Rule_db.Ar3_f ->
    (* AR3_F: rewrite the `¬(a ≤ 𝟎)` occurrence to `r ≤ 𝟎` in place, at PP's
       position.  Build the congruence proof `goal = goal'` for that exact
       (binder-nested) occurrence and transport the live goal with `=⇒`; the
       child then proves the normalised `goal'`.  `(a, r)` come from the
       PipeArg.  Falls back to a no-op when the occurrence isn't on a
       supported path or the `𝟏 − a = r` equality can't be built. *)
    let tactic_opt =
      match goal, arg with
      | Some g, Some (PipeArg (a_exp, r_exp)) ->
        Option.map
          (fun cong ->
            L.Refine (L.Name "=⇒", [L.App (L.Name "eq_sym", [cong]); L.Hole]))
          (ar3f_cong ctx (proj_env_of_ctx ctx) (flatten_binds g) a_exp r_exp)
      | _ -> None
    in
    (match tactic_opt with
     | Some tactic -> L.Then (tactic, tree ctx c)
     | None -> tree ctx c)
  | [c], Rule_db.Ar7_8 ->
    (* AR7/AR8.  The child IMP4 introduces the solver antisymmetry equality,
       recorded bare-variable-first (`b = a`); its sides give a (= rhs) and
       b (= lhs).  AR7's bound hyp is `(c+b) = (b−a) ≤ 𝟎`, AR8's is `(a−b) ≤ 𝟎`
       — recover it from scope (directly or term-reordered) as a real proof via
       [leaf_evidence]; only the solver fact `a+c = 𝟎` is `trust`.  a/b/c are
       inferred from that hyp proof and the goal, so the explicit value slot is
       a hole, and the `hR` slot is filled by the child continuation.  If the
       hyp isn't recoverable, fall through to the explicit AR7/AR8 failure. *)
    (* AR7's bound hyp and explicit slot are `c`-shaped: `c + b ≤ 𝟎` with the
       explicit value `c = —a`, so the proof must be in `(—a + b)` form to unify.
       AR8's are `a`-shaped: `a − b ≤ 𝟎`, explicit `a` inferred from that proof. *)
    let is_ar7 = base rule = "AR7" in
    let hbound_and_val =
      match goal_of_anno (P.anno_of c) with
      | Some (Binary (Imp, Eq (lhs_e, rhs_e), _)) ->
        let hyp_lhs, value =
          if is_ar7 then AOp (Add, Neg rhs_e, lhs_e),
                         L.Exp (proj_env_of_ctx ctx, Neg rhs_e)
          else AOp (Sub, rhs_e, lhs_e), L.Hole
        in
        Option.map (fun hb -> (hb, value))
          (leaf_evidence ctx [] (Leq (hyp_lhs, Nat 0)))
      | _ -> None
    in
    (match hbound_and_val with
     | Some (hb, value) ->
       let tactic =
         L.Refine (L.Name (base rule), [value; hb; L.Trust; L.Hole]) in
       L.Then (tactic, tree ctx c)
     | None ->
       L.Then (tactic_for_rule ctx rule arg anno children, tree ctx c))
  | _, _ ->
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
    | [c] when Rule_db.binds_var rule ->
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
  let pp_vars = branch_binder_vars rule (goal_of_anno anno) in
  let tactic = L.Refine (L.Name (base rule), [L.Hole; L.Hole]) in
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
and chain_tree ctx node =
  match node with
  | P.Apply { rule; src_line; anno; _ } ->
    L.Commented (prov_of rule src_line anno, chain_dispatch ctx node)

and chain_dispatch ctx = function
  | P.Apply { rule; children = []; arg; _ } ->
    let args = dynamic_value_args ctx rule arg @ slot_hole_args rule in
    L.Step (L.Refine (L.Name (chain_emit_name rule), args))
  | P.Apply { rule; anno; children = [c]; _ } when Rule_db.binds_var rule ->
    let pp_vars =
      match goal_of_anno anno with
      | Some g -> Option.value ~default:[] (binder_vars_of g)
      | None -> []
    in
    let x = fresh_x ctx pp_vars in
    let tactic = L.Refine (L.Name rule, [L.Hole]) in
    L.Assume_then (tactic, x, chain_tree ctx c)
  | P.Apply { rule; anno; children = [c]; _ }
    when Rule_db.emit rule = Rule_db.Opr false
         || Rule_db.emit rule = Rule_db.Opr true ->
    (* Bind a fresh `_xN` (PP vars never start with `_`, so it cannot be
       captured by a variable already free in `consequent`).  OPR1 rewrites
       the equality's LHS var, OPR2 (rtl) the RHS var. *)
    let rtl = Rule_db.emit rule = Rule_db.Opr true in
    let z = fresh_x_local ctx in
    let p_lambda =
      match goal_of_anno anno with
      | Some (Binary (Imp, Eq (lhs, rhs), consequent)) ->
        (match (if rtl then rhs else lhs) with
         | Var v ->
           L.Lambda (z, Some L.Tau_i,
             pred_term ctx (subst_prd [(v, Var z)] consequent))
         | _ -> L.Hole)
      | _ -> L.Hole
    in
    let tactic = L.Refine (L.Name rule, [p_lambda] @ slot_hole_args rule) in
    L.Then (tactic, chain_tree ctx c)
  | P.Apply { rule; arg; children = [c]; _ }
    when Rule_db.emit rule = Rule_db.Ar10 ->
    (* AR10_1 [P Q R] (heq : P = Q) (r : Res (Q ⇒ R)) : Res (P ⇒ R).
       Q is the solver result and can't be inferred from P ⇒ R alone, so
       supply it explicitly (env-carried) with `trust` for the equality;
       the chain continuation fills the Res hole.  Mirrors the main-tree
       AR10 dispatch. *)
    let q_term = match arg with
      | Some (Pred q) -> pred_term ctx q
      | _ -> L.Hole
    in
    let tactic =
      L.Refine (L.Expl (L.Name rule), [L.Hole; q_term; L.Hole; L.Trust; L.Hole])
    in
    L.Then (tactic, chain_tree ctx c)
  | P.Apply { rule; arg; anno; children = [c]; _ }
    when Rule_db.emit rule = Rule_db.Ar3 ->
    (* AR3 in a Res chain.  PP's solver records the sub-premise `𝟏 - a` in a
       different (neg-normalised) term order `r` (the arg), so the plain AR3_1
       — which expects the continuation typed at `𝟏 - a` — leaves `a` unsolved.
       Emit the bridged AR3'_1: `a` from the goal `¬(a≤𝟎) ⇒ R`, `r` from the
       arg, and a *generated* proof `𝟏 - a = r` (no `trust`).  Fall back to the
       generic AR3_1 path when the shape is unexpected. *)
    let env = proj_env_of_ctx ctx in
    let bridged =
      match goal_of_anno anno, arg with
      | Some (Binary (Imp, Unary (Not, Leq (a_exp, Nat 0)), _)), Some (Pred (Lift r_exp)) ->
        Option.map
          (fun eqpf ->
            L.Refine (L.Name "AR3'_1",
              [L.Exp (env, a_exp); L.Exp (env, r_exp); eqpf; L.Hole]))
          (prove_sum_eq env (AOp (Sub, Nat 1, a_exp)) r_exp)
      | _ -> None
    in
    let tactic =
      match bridged with
      | Some t -> t
      | None ->
        L.Refine (L.Name (chain_emit_name rule),
                  dynamic_value_args ctx rule arg
                  @ metadata_extra_args rule @ slot_hole_args rule)
    in
    L.Then (tactic, chain_tree ctx c)
  | P.Apply { rule; arg; children = [c]; _ } ->
    (* Mirror the main-tree arg bundle: dynamic value args, then the solver
       side-condition metadata (AR9's `trust` for `E = F`), then slot holes.
       The chain path used to drop the metadata, so AR9_1 emitted without its
       `trust` and left the `he` goal unfilled ("missing subproofs"). *)
    let tactic =
      L.Refine (L.Name (chain_emit_name rule),
                dynamic_value_args ctx rule arg
                @ metadata_extra_args rule @ slot_hole_args rule)
    in
    L.Then (tactic, chain_tree ctx c)
  | P.Apply { rule; anno; children = [c0; c1]; _ }
    when Rule_db.is_branching (base rule) ->
    (* ALL7_1 / XST8_1 inside a Res chain: a per-tuple Res chain ρ (under
       the bound v) plus the continuation r.  Mirrors `branching` but stays
       in Res mode — the ρ child must bind v, exactly like the main-tree
       form, otherwise its `Π v, Res …` goal is left unproven. *)
    let pp_vars = branch_binder_vars rule (goal_of_anno anno) in
    let tactic = L.Refine (L.Name rule, [L.Hole; L.Hole]) in
    let v = fresh_x_local ctx in
    let rho = scoped_hyps ctx (fun () ->
      with_x ctx v pp_vars (fun () -> L.Assume (v, chain_tree ctx c0)))
    in
    let cont = scoped_hyps ctx (fun () -> chain_tree ctx c1) in
    L.Branches (tactic, rho, cont)
  | P.Apply { rule; arg; children = [c0; c1]; _ } ->
    let tactic =
      L.Refine (L.Name (chain_emit_name rule),
                dynamic_value_args ctx rule arg @ slot_hole_args rule)
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
