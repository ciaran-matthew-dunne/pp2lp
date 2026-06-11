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
  | P.Apply { rule; children = [c]; _ }
    when Rule_db.emit rule = Rule_db.Egalite ->
    (* EGALITE (the equality-prover terminal): PP rewrites the store's hyps
       along the stored equalities and re-promotes them as antecedents over
       the ⊥ goal; the child proves that implication chain.  Emit
       `refine (λ k : π (chain), k ev₁ … evₙ) _` — the typed λ pins the
       child goal (a bare `refine _ ev…` leaves it undetermined), each evᵢ a
       direct hyp or an `ind_eq`-transported one ([Emit_ctx.leaf_evidence]'s
       equality-store bridge). *)
    (match goal_of_anno (P.anno_of c) with
     | Some child_goal ->
       let rec peel acc = function
         | Binary (Imp, a, rest) -> peel (a :: acc) rest
         | _ -> List.rev acc
       in
       let antecedents = peel [] child_goal in
       if antecedents = [] then
         failwith "translate: EGALITE child goal has no antecedents \
                   (expected the rewritten-hyp implication chain)";
       let evs =
         List.map (fun a ->
           match leaf_evidence ctx [] a with
           | Some ev -> ev
           | None ->
             failwith (Printf.sprintf
               "translate: EGALITE — no in-scope hyp matches the rewritten \
                antecedent (directly or modulo a stored equality)\n  \
                antecedent: %s" (Emit_pp.prd_to_pp a)))
           antecedents
       in
       let k = fresh_x_local ctx in
       let cut =
         L.Lambda (k, Some (L.Pi_pred (proj_env_of_ctx ctx, child_goal)),
                   L.App (L.Name k, evs))
       in
       L.Then (L.Refine (cut, [L.Hole]), tree ctx c)
     | None -> failwith "translate: EGALITE child has no annotation")
  | P.Apply { rule; anno; children = [c]; _ }
    when Rule_db.emit rule = Rule_db.Eqs2 ->
    (* PP's EQS2 (spec p.98) discharges ¬eql_set(E,F) with a FAUX ⇒ R
       child: the marker's content is still in PP's hypothesis store.  An
       assumed `E = F` (via set_ext) or marker hyp feeds the EQS2 lemma's
       evidence slot, and the child proves ⊥ ⇒ R.  When the marker is
       instead still an antecedent *inside R*, close the implication with
       a generated intro+projection term and drop the placeholder child
       (precedent: Witness_hyp). *)
    (match goal_of_anno anno with
     | Some (Binary (Imp, Unary (Not, Lift (App (g, [e; f]))), r))
       when g = "_eql_set" || g = "eql_set" ->
       (match find_eqs2_hyp ctx e f with
        | Some (h, is_eq) ->
          let ev =
            if is_eq then
              L.App (L.Name "\xe2\x88\xa7\xe2\x82\x91\xe2\x82\x81", (* ∧ₑ₁ *)
                [L.App (L.Name "set_ext", [exp_term ctx e; exp_term ctx f]);
                 L.Name h])
            else L.Name h
          in
          L.Then (L.Refine (L.Name "EQS2", [ev; L.Hole]), tree ctx c)
        | None ->
          match find_eqs2_incl_pair ctx e f with
          | Some (h1, h2) ->
            let ev =
              L.App (L.Name "eql_set_intro", [L.Name h1; L.Name h2]) in
            L.Then (L.Refine (L.Name "EQS2", [ev; L.Hole]), tree ctx c)
          | None ->
          (match find_eqs2_spine e f r with
           | Some (n_before, path) ->
             let hneg = fresh_x_local ctx in
             let hc = fresh_x_local ctx in
             let rec inits t m =
               if m = 0 then t
               else inits (L.App (L.Name "\xe2\x8b\x80_init", [t])) (m - 1)
             in
             let peel =
               List.fold_left
                 (fun t (n_conjs, k) ->
                    L.App (L.Name "\xe2\x8b\x80_last",
                           [inits t (n_conjs - 1 - k)]))
                 (L.Name hc) path
             in
             let body =
               L.App (L.Name "\xe2\x8a\xa5\xe2\x82\x91", (* ⊥ₑ *)
                      [L.App (L.Name hneg, [peel])])
             in
             let rec wrap m t =
               if m = 0 then t
               else wrap (m - 1) (L.Lambda (fresh_x_local ctx, None, t))
             in
             let term =
               L.Lambda (hneg, None, wrap n_before (L.Lambda (hc, None, body)))
             in
             L.Step (L.Refine (term, []))
           | None ->
             let hyps =
               String.concat "\n"
                 (List.map (fun (n, p) ->
                    Printf.sprintf "    %s : %s" n (Emit_pp.prd_to_pp p))
                    ctx.hyps)
             in
             failwith (Printf.sprintf
               "translate: EQS2 — no eql_set evidence found (neither an \
                assumed `E = F`/marker hyp nor a marker antecedent in R's \
                spine)\n  hyps in scope:\n%s" hyps)))
     | _ -> default ctx rule None anno [c])
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
  | [c], Rule_db.Nrm2730 ->
    (* NRM27-30: trust-free arithmetic-solver dispatch.  Peel the pinned
       binder at the witness `b`, then bridge the literal substituted
       conjunction `⋀ (ps (v' ⨾ b v'))` to ⊤ (matching PP's ⊤-normalisation)
       with a generated congruence proof, and the continuation child proves
       the ⊤-form `♢v'·¬⊤ ⇒ R`.  Only NRM29 (the multi-binder ⇒R form) is
       exercised by the corpus; the unary 28/30 and bare 27 fail loudly. *)
    (match base rule with
     | "NRM29" ->
       (match goal with
        | Some g ->
          (match Emit_ctx.nrm29_witness_bridge ctx g with
           | Some (b, cong) ->
             L.Then (L.Refine (L.Name "NRM29", [b; L.Hole]),
               L.Then (L.Refine (L.Name "=⇒",
                         [L.App (L.Name "eq_sym", [cong]); L.Hole]),
                 tree ctx c))
           | None ->
             failwith "translate: NRM29 goal is not the cancelling-bounds shape \
                       (♡(d,…)·¬⋀(d+r≤𝟎 ∧ —d−r≤𝟎) ⇒ R); the solver witness \
                       can't be reconstructed")
        | None -> failwith "translate: NRM29 has no goal annotation")
     | other ->
       failwith (Printf.sprintf
         "translate: %s trust-free dispatch unsupported — no corpus trace \
          exercises it (only NRM29 is wired)" other))
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
       (* The solver fact `(a + c) = 𝟎` is a cancellation (a = `rhs_e`, the
          antisymmetry RHS; c = —a) — [prove_sum_zero], no trust.  For AR7 c is
          the explicit value `—rhs_e`; for AR8 c is *goal-inferred* (the left
          summand of the goal antecedent `c + b`, b = lhs_e), so read it from
          there or the distributed form won't unify with `—rhs_e`.  Trust only
          if the shape is off. *)
       let acc_eq =
         let env = proj_env_of_ctx ctx in
         match goal_of_anno (P.anno_of c) with
         | Some (Binary (Imp, Eq (lhs_e, rhs_e), _)) ->
           let ac =
             if is_ar7 then Some (AOp (Add, rhs_e, Neg rhs_e))
             else
               (match goal_of_anno anno with
                | Some (Binary (Imp, Leq (AOp (Add, c_e, b_e), Nat 0), _))
                  when b_e = lhs_e -> Some (AOp (Add, rhs_e, c_e))
                | _ -> None)
           in
           (match ac with
            | Some ac -> Option.value ~default:L.Trust (prove_sum_zero env ac)
            | None -> L.Trust)
         | _ -> L.Trust
       in
       let tactic =
         L.Refine (L.Name (base rule), [value; hb; acc_eq; L.Hole]) in
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
  (* Pass the Res chain as an *explicit term* (`refine ALL7 (λ v, …) _`)
     rather than a `{assume v; …}` subproof.  The block form leaves the
     chain ρ as a metavariable while its block elaborates; under *nested*
     branchings the enclosing goal still contains `res_tm ?ρ`, and
     unifying the inner branching's conclusion against that flex term
     picks garbage solutions (e.g. a constant `?P := λ _, res_tm CHAIN`).
     An explicit ρ fully determines the conclusion type up front. *)
  let pp_vars = branch_binder_vars rule (goal_of_anno anno) in
  let v = fresh_x_local ctx in
  let rho = scoped_hyps ctx (fun () ->
    with_x ctx v pp_vars (fun () ->
      L.Lambda (v, None, chain_term ctx chain_node)))
  in
  let tactic = L.Refine (L.Name (base rule), [rho; L.Hole]) in
  let cont_proof = scoped_hyps ctx (fun () -> branch_cont ctx cont) in
  L.Then (tactic, cont_proof)

(* A branching continuation's goal is `(!! v, res_tm (ρ v)) ⇒ R`.  When the
   chain result is itself a universal, that antecedent is *structurally
   nested* (`!! v, !! y, …`) — unlike everywhere else, where the renderer
   already merges nested PP binders into one compound tuple (which is why
   ALL3 is a HOAS identity by default).  Here PP's ALL3 merge must be
   emitted for real, as ALL3R: its compound premise appends the *outer*
   element last, matching the renderer's slot order (first PP binder ↦
   prj 0), so downstream hyp searches stay consistent.  P sits applied at
   a tuple constructor — a non-pattern position lambdapi cannot invert —
   so it is passed explicitly, built from the child's merged annotation. *)
and branch_cont ctx cont =
  match cont with
  | P.Apply { rule; children = [c]; src_line; anno; _ }
    when base rule = "ALL3" ->
    let merged =
      match c with
      | P.Apply { anno = canno; _ } ->
        (match goal_of_anno canno with
         | Some (Binary (Imp, Bind (_, vars, body), _)) -> Some (vars, body)
         | _ -> None)
    in
    (match merged with
     | Some (vars, body) ->
       let u = fresh_x_local ctx in
       let p_lambda =
         with_x ctx u vars (fun () -> L.Lambda (u, None, pred_term ctx body))
       in
       let tactic = L.Refine (L.Expl (L.Name "ALL3R"),
         [L.Hole; p_lambda; L.Hole; L.Hole]) in
       L.Commented (prov_of rule src_line anno, L.Then (tactic, tree ctx c))
     | None -> tree ctx cont)
  | _ -> tree ctx cont

(* The Res-chain handed to ALL7/XST8 has type `Π v : Tuple n, Res (P v)`.
   Build it as an explicit *term*: chains are purely applicative (each step
   is a rule symbol applied to value args and child sub-chains), and an
   explicit ρ keeps a nested branching's conclusion fully determined (see
   `branching`).  Child sub-chains plug into the *trailing* argument slots
   (`slot_hole_args` puts child slots last). *)
and chain_term ctx node : L.term =
  let app name = function [] -> L.Name name | args -> L.App (L.Name name, args) in
  let plug rule args children =
    let n = List.length args - List.length children in
    if n < 0 then
      failwith (Printf.sprintf
        "translate: chain %s has fewer arg slots than children" rule);
    let prefix = List.filteri (fun i _ -> i < n) args in
    let slots = List.filteri (fun i _ -> i >= n) args in
    List.iter (function
      | L.Hole -> ()
      | _ -> failwith (Printf.sprintf
               "translate: chain %s child slot is not a hole" rule)) slots;
    prefix @ children
  in
  match node with
  | P.Apply { rule; anno; children = []; _ }
    when base rule = "AXM9" && (match goal_of_anno anno with
                                | Some (Binary (Imp, _, _)) -> true
                                | _ -> false) ->
    (* AXM9_1 [n] [P] (v) [Q] (h) : Res (P v ⇒ Q).  Recover the witness `v`
       and the universal hyp `h` exactly as the base AXM9 does — `P` infers
       from `h` (a Miller pattern), so the result type is determined without
       the old `@inh_tuple` constant-P hack and the `trust` it forced. *)
    (match goal_of_anno anno with
     | Some goal ->
       (match find_axm9_match ctx goal with
        | Some (witness, h) ->
          L.App (L.Name (chain_emit_name rule), [witness; L.Name h])
        | None ->
          failwith "translate: AXM9_1 — no (witness × universal hyp) match for \
                    the chain antecedent")
     | None -> assert false)
  | P.Apply { rule; anno; children = []; _ }
    when (match base rule with
          | "AXM1" | "AXM2" | "AXM3" | "AXM4" | "AXM5" | "AXM6" -> true
          | _ -> false) ->
    (* Chain-form AXM1-6 (Schema 0): the `_1` lemma needs the same hyp the
       base rule looks up.  Recover it from scope as a real proof term
       ([leaf_evidence] also bridges arith-reorder / equality-store shapes);
       the LP lemma reuses the base rule + `prop_eq_top`.  No hyp recovered ⇒
       `trust`, matching the pre-evidence behaviour (no regression). *)
    let ev =
      match goal_of_anno anno with
      | Some goal ->
        (match expected_hyp_pred rule goal with
         | Some needed -> Option.value ~default:L.Trust (leaf_evidence ctx [] needed)
         | None -> L.Trust)
      | None -> L.Trust
    in
    L.App (L.Name (chain_emit_name rule), [ev])
  | P.Apply { rule; anno; children = []; _ } when base rule = "AXM8" ->
    (* Chain-form AXM8: the conjunct-extraction `π C → π r` the base rule
       builds, handed to AXM8_1 (which wraps it in `mk_0 ∘ prop_eq_top`). *)
    let f = Option.value ~default:L.Trust (axm8_extraction ctx anno) in
    L.App (L.Name (chain_emit_name rule), [f])
  | P.Apply { rule; children = []; arg; _ } ->
    app (chain_emit_name rule)
      (dynamic_value_args ctx rule arg @ slot_hole_args rule)
  | P.Apply { rule; anno; children = [c]; _ } when Rule_db.binds_var rule ->
    let pp_vars =
      match goal_of_anno anno with
      | Some g -> Option.value ~default:[] (binder_vars_of g)
      | None -> []
    in
    let x = fresh_x ctx pp_vars in
    app rule [L.Lambda (x, None, chain_term ctx c)]
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
    app rule
      (plug rule ([p_lambda] @ slot_hole_args rule) [chain_term ctx c])
  | P.Apply { rule; arg; children = [c]; _ }
    when Rule_db.emit rule = Rule_db.Ar10 ->
    (* AR10_1 [P Q R] (heq : P = Q) (r : Res (Q ⇒ R)) : Res (P ⇒ R).
       Q is the solver result and can't be inferred from P ⇒ R alone, so
       supply it explicitly (env-carried).  PP's `solveur(P) = Q` is the
       identity (P ≡ Q), so the equality is `eq_refl Q`, not `trust`.
       Mirrors the main-tree AR10 dispatch. *)
    let q_term = match arg with
      | Some (Pred q) -> pred_term ctx q
      | _ -> L.Hole
    in
    let heq = match arg with
      | Some (Pred _) -> L.App (L.Name "eq_refl", [q_term])
      | _ -> L.Trust
    in
    L.App (L.Expl (L.Name rule),
      [L.Hole; q_term; L.Hole; heq; chain_term ctx c])
  | P.Apply { rule; arg; children = [c]; _ }
    when Rule_db.emit rule = Rule_db.Ar9 ->
    (* AR9_1 (F) (he : E = F) (r : Res ((F ≤ 𝟎) ⇒ R)) : Res ((E ≤ 𝟎) ⇒ R).
       PP's `solveur(E) = F` is the identity (E ≡ F), so `he` is `eq_refl F`,
       not `trust`.  Mirrors the main-tree AR9 dispatch. *)
    (match dynamic_value_args ctx rule arg with
     | [f] ->
       app (chain_emit_name rule)
         [f; L.App (L.Name "eq_refl", [f]); chain_term ctx c]
     | _ ->
       app (chain_emit_name rule)
         (plug rule
            (dynamic_value_args ctx rule arg
             @ metadata_extra_args rule @ slot_hole_args rule)
            [chain_term ctx c]))
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
            L.App (L.Name "AR3'_1",
              [L.Exp (env, a_exp); L.Exp (env, r_exp); eqpf; chain_term ctx c]))
          (prove_sum_eq env (AOp (Sub, Nat 1, a_exp)) r_exp)
      | _ -> None
    in
    (match bridged with
     | Some t -> t
     | None ->
       app (chain_emit_name rule)
         (plug rule
            (dynamic_value_args ctx rule arg
             @ metadata_extra_args rule @ slot_hole_args rule)
            [chain_term ctx c]))
  | P.Apply { rule; anno; children = [c]; _ }
    when base rule = "IMP5" ->
    (* IMP5_1 (hp : π P) (r : Res Q) : Res (P ⇒ Q) — strips a *known*
       antecedent, so its result list collapses the ⇒; the proof hp lives
       in the store.  Find it by the annotation's antecedent. *)
    (match goal_of_anno anno with
     | Some (Binary (Imp, p, _)) ->
       (match find_hyp_by_pred ctx p with
        | Some h ->
          L.App (L.Name (chain_emit_name rule), [L.Name h; chain_term ctx c])
        | None ->
          failwith "translate: IMP5_1 — the known-antecedent hyp is not in \
                    scope")
     | _ ->
       failwith "translate: IMP5_1 expected an implication annotation")
  | P.Apply { rule; children = [c]; _ }
    when base rule = "ALL3"
         && (match c with
             | P.Apply { anno = canno; _ } ->
               (match goal_of_anno canno with
                | Some (Binary (Imp, Bind (_, _, _), _)) -> true
                | _ -> false)) ->
    (* Chain form of the explicit-P ALL3R emission (see `branch_cont`). *)
    (match c with
     | P.Apply { anno = canno; _ } ->
       (match goal_of_anno canno with
        | Some (Binary (Imp, Bind (_, vars, body), _)) ->
          let u = fresh_x_local ctx in
          let p_lambda =
            with_x ctx u vars (fun () -> L.Lambda (u, None, pred_term ctx body))
          in
          L.App (L.Expl (L.Name "ALL3R_1"),
            [L.Hole; p_lambda; L.Hole; chain_term ctx c])
        | _ -> assert false))
  | P.Apply { rule; arg; children = [c]; _ } ->
    (* Mirror the main-tree arg bundle: dynamic value args, then the solver
       side-condition metadata (AR9's `trust` for `E = F`), then slot holes.
       The chain path used to drop the metadata, so AR9_1 emitted without its
       `trust` and left the `he` goal unfilled ("missing subproofs"). *)
    app (chain_emit_name rule)
      (plug rule
         (dynamic_value_args ctx rule arg
          @ metadata_extra_args rule @ slot_hole_args rule)
         [chain_term ctx c])
  | P.Apply { rule; anno; children = [c0; c1]; _ }
    when Rule_db.is_branching (base rule) ->
    (* ALL7_1 / XST8_1 inside a Res chain: a per-tuple Res chain ρ (under
       the bound v) plus the continuation r — both explicit terms. *)
    let pp_vars = branch_binder_vars rule (goal_of_anno anno) in
    let v = fresh_x_local ctx in
    let rho = scoped_hyps ctx (fun () ->
      with_x ctx v pp_vars (fun () ->
        L.Lambda (v, None, chain_term ctx c0)))
    in
    let cont = scoped_hyps ctx (fun () -> chain_term ctx c1) in
    app rule [rho; cont]
  | P.Apply { rule; arg; children = [c0; c1]; _ } ->
    let left = scoped_hyps ctx (fun () -> chain_term ctx c0) in
    let right = scoped_hyps ctx (fun () -> chain_term ctx c1) in
    app (chain_emit_name rule)
      (plug rule
         (dynamic_value_args ctx rule arg @ slot_hole_args rule)
         [left; right])
  | P.Apply { rule; children; _ } ->
    failwith (Printf.sprintf
      "translate: chain %s arity %d unsupported"
      rule (List.length children))

(* The BOOL31/32/41/42 emit accumulates its `V ϵ BOOL` typing premises into
   [ctx.bool_typings] as it fires (it needs the in-scope tuple binder, only
   known mid-walk); return them alongside the script so [Emit_lp] adds them to
   the symbol header. *)
let translate (pp_tree : P.pp_tree) : L.t * (string * string) list =
  let ctx = create_ctx () in
  let script = tree ctx pp_tree in
  (script, ctx.bool_typings)
