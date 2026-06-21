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

(* The solver-result *predicate* carried by a rule arg: a [Pred] directly, a bare
   [ExpArg] re-lifted to a proposition (a boolean expression in prop position).
   [PipeArg]/absent → None.  Used by AR10/AR10_1's no-op sanity warning. *)
let arg_prd : arg option -> prd option = function
  | Some (Pred q) -> Some q
  | Some (ExpArg e) -> Some (Lift e)
  | _ -> None

(* Binder vars introduced by a branching quantifier, read from its goal
   annotation: ALL7's goal is `(binder) ⇒ R`, XST8's is the bare binder.
   Shared by the main-tree [branching] and the Res-chain branch case. *)
let branch_binder_vars rule goal =
  match base rule, goal with
  | "ALL7", Some (Binary (Imp, b, _)) -> Option.value ~default:[] (binder_vars_of b)
  | "XST8", Some g -> Option.value ~default:[] (binder_vars_of g)
  | _ -> []

(* Does the Res-chain subtree [node] contain an AXM1-6 leaf that looks up the
   predicate [pred]?  Used at a chain `IMP4_1` to decide whether its antecedent
   has to be threaded down to a chain-local AXM (which otherwise trusts). *)
let rec chain_looks_up node pred =
  match node with
  | P.Apply { rule; anno; children; _ } ->
    let here =
      (match base rule with
       | "AXM1" | "AXM2" | "AXM3" | "AXM4" | "AXM5" | "AXM6" | "IMP5" ->
         (match goal_of_anno anno with
          | Some g -> expected_hyp_pred rule g = Some pred
          | None -> false)
       | _ -> false)
    in
    here || List.exists (fun c -> chain_looks_up c pred) children

(* AR3_F congruence-path builder.  PP's forward normalisation rewrites a
   `¬(a ≤ 𝟎)` occurrence to `r ≤ 𝟎` *in place*, wherever it sits in the
   binder-nested goal.  Build the propositional-equality proof `goal = goal'`
   for that exact position by recursing down to the occurrence, composing one
   congruence lemma per connective on the path (`imp_cong_l/r`, `not_cong`,
   `conj_snoc_last_cong`, `!!_cong` under a binder), terminating in `ar3f_eq`;
   the caller transports the live goal with `=⇒`.  `env` renders binder-bound
   vars as `prj k v` — compound NRM8/9 binders included, via the
   `prj`-through-`take`/`drop` rules in B.lp.  None when the occurrence
   isn't found on a supported path (caller then falls back to a no-op). *)
let rec ar3f_cong ctx env binders prd a_exp r_exp : L.term option =
  match prd with
  | Unary (Not, Leq (a', Lit "0")) when a' = a_exp ->
    Option.map
      (fun eqpf -> L.App (L.Name "ar3f_eq",
        [ L.Exp (env, a_exp); L.Exp (env, r_exp); eqpf ]))
      (* The `𝟏 − a = r` proof is a reflective TERM (`toint_eq … (reflect …)`),
         so it sits directly inside this enclosing `!!_cong (λ v, …)` occurrence —
         no Π-quantified `have` to hoist. *)
      (Arith_proofs.prove_sum_eq env (AOp (Sub, Lit "1", a_exp)) r_exp)
  | Unary (Not, p) ->
    Option.map (fun c -> L.App (L.Name "not_cong", [c]))
      (ar3f_cong ctx env binders p a_exp r_exp)
  | Binary (Imp, p, q) ->
    (match ar3f_cong ctx env binders p a_exp r_exp with
     | Some c -> Some (L.App (L.Name "imp_cong_l", [c]))
     | None ->
       Option.map (fun c -> L.App (L.Name "imp_cong_r", [c]))
         (ar3f_cong ctx env binders q a_exp r_exp))
  | Binary (And, _, last) ->
    Option.map (fun c -> L.App (L.Name "conj_snoc_last_cong", [c]))
      (ar3f_cong ctx env binders last a_exp r_exp)
  | Bind (_, vars, body) ->
    let v = fresh_x_local ctx in
    let env' = List.mapi (fun k var -> (var, L.Proj (k, v))) vars @ env in
    (* Register the binder in ctx.xs (not just the render env) so an integer-typed
       bound var used arithmetically under here resolves its `ϵ INT` evidence
       against the in-scope projection (the typing oracle applies to `v ⋕ k`);
       thread it onto [binders] too so the equality `have` quantifies it (the
       proof lives at tactic scope, applied to v here). *)
    Option.map (fun c -> L.App (L.Name "!!_cong", [L.Lambda (v, None, c)]))
      (with_x ctx v vars (fun () ->
         ar3f_cong ctx env' (binders @ [ (v, List.length vars) ]) body a_exp r_exp))
  | _ -> None

(* Closer for a residual bool-literal disequality `¬(b1 = b2)` (b1 ≠ b2):
   `bool_distinct` proves `¬(BTRUE = BFALSE)`, its `eq_sym` mirror the reverse
   orientation.  Terminal OPR1/OPR2 (after rewriting x ↦ E) and terminal EVR3
   (after the trivial `E = E` antecedent) land on such a residual when PP closes
   a boolean goal in one step.  None ⇒ not trivially closable. *)
let bool_diseq_closer : prd -> L.term option = function
  | Unary (Not, Eq (Var ("TRUE" | "VRAI"), Var ("FALSE" | "FAUX"))) ->
    Some (L.Name "bool_distinct")
  | Unary (Not, Eq (Var ("FALSE" | "FAUX"), Var ("TRUE" | "VRAI"))) ->
    Some (L.Lambda ("h", None,
      L.App (L.Name "bool_distinct", [ L.App (L.Name "eq_sym", [ L.Name "h" ]) ])))
  | _ -> None

(* Does an expression contain an arithmetic operator?  A set-equality marker side
   that does is a misparse (e.g. set difference `s - t` lexes as arithmetic
   `minus`), which has no membership-unfolding rule — proving the marker from the
   inclusions would then leave lambdapi churning, so [eqs2_marker_reuse] skips it. *)
let rec exp_has_arith e =
  match e with
  | AOp _ | Neg _ -> true
  | _ -> fold_exp (fun acc sub -> acc || exp_has_arith sub) false e

let rec tree ctx node =
  match node with
  | P.Apply { rule; children = [c]; _ }
    when Rule_db.is_hoas_identity (base rule) ->
    (* Skip to the child — [hoas_identity] (ALL6): the transformation is
       LP-definitional (¬Q ≡ Q⇒⊥), so parent and child goals are convertible and
       the rule emits no tactic of its own.

       The §A.7–8 quantifier regroupement rules (ALL1–4 / XST1–4) are NOT skipped:
       they are emitted for real.  Goals render with their binders nested
       (flatten_binds is gone), and each merge rule is curried (`!! w, !! y, P w y`,
       a pattern → `refine NAME _` infers P), so it flows through the [Default] path
       below as `refine NAME _; <child>` — the take/drop premise reduces to exactly
       the compound `Tuple n` slot order the downstream ALL7/NRM/… already expect. *)
    tree ctx c
  | P.Apply { rule; arg; anno; children = [c]; _ }
    when Rule_db.emit rule = Rule_db.Ar10 ->
    (* AR10 [P Q R] : π (P = Q) → π (Q ⇒ R) → π (P ⇒ R).  Usually PP's
       `solveur(P) = Q` is the identity (P ≡ Q), so the goal `P ⇒ R` and the
       child's `Q ⇒ R` are convertible and we skip straight to the child — no
       `refine AR10 …` at all.  When PP's recorded Q diverges from the goal
       antecedent P, the solver did real arithmetic normalisation (e.g. `-(-x)=x`
       ↦ `x=x`); P and Q are then not convertible, so emit a genuine `refine AR10
       <P = Q> _` with the propositional-equality proof from [prove_pred_eq].
       Fall back to the bare skip (warning) for shapes that helper can't bridge —
       the skip then fails loud at the lambdapi check rather than silently. *)
    (match goal_of_anno anno, arg_prd arg with
     | Some (Binary (Imp, p, _)), Some q when p <> q ->
       (match Arith_proofs.prove_pred_eq (proj_env_of_ctx ctx) p q with
        | Some pf -> L.Then (L.Refine (L.Name "AR10", [pf; L.Hole]), tree ctx c)
        | None ->
          Errors.warn
            "AR10 skipped as a no-op, but its solver result Q differs from the \
             goal antecedent P — P ≡ Q is assumed (P = %s ; Q = %s); if they are \
             not convertible the skipped child will fail to type-check"
            (Emit_pp.prd_to_pp p) (Emit_pp.prd_to_pp q);
          tree ctx c)
     | _ -> tree ctx c)
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
     | Some script -> script
     | None ->
       let goal = match goal_of_anno anno with
         | Some g -> Emit_pp.prd_to_pp g
         | None -> "(no annotation)"
       in
       Errors.fail "E_INS"
         "INS contradiction search failed — no (universal hyp \xc3\x97 witness) \
          discharges every conjunct\n  goal: %s\n%s"
         goal (ins_diagnostic ctx))
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
             let dump =
               if Sys.getenv_opt "PP2LP_DEBUG_EGALITE" = None then ""
               else "\n  hyps in scope:\n" ^ String.concat "\n"
                 (List.map (fun (n, p) ->
                    Printf.sprintf "    %s : %s" n (Emit_pp.prd_to_pp p))
                    ctx.hyps)
             in
             failwith (Printf.sprintf
               "translate: EGALITE — no in-scope hyp matches the rewritten \
                antecedent (directly or modulo a stored equality)\n  \
                antecedent: %s%s" (Emit_pp.prd_to_pp a) dump))
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
    when base rule = "EQS1" ->
    (* EQS1 lifts `eql_set E F ⇒ R` to `(E = F) ⇒ R`.  `eql_set E F` unfolds to
       `∀a, a ϵ E ⇔ a ϵ F`, and when F is a set-algebra op (union/inter/diff/∅)
       the membership `a ϵ F` unfolds further (∨ / ⋀ / ⊥), so lambdapi can't infer
       the implicit F from the goal — `a ϵ ?F` won't unify against the unfolded
       body.  Supply E and F explicitly (`@EQS1 E F _ _`); R is inferred from the
       goal and the trailing hole is the `(E = F) ⇒ R` child.  (For an irreducible
       F — `interval …` — plain `refine EQS1 _` also works, but the explicit form
       is uniform and equally valid.) *)
    (match goal_of_anno anno with
     | Some (Binary (Imp, Lift (App (g, [e; f])), _))
       when g = "_eql_set" || g = "eql_set" ->
       L.Then (L.Refine (L.Expl (L.Name "EQS1"),
                         [exp_term ctx e; exp_term ctx f; L.Hole; L.Hole]),
               tree ctx c)
     | _ -> default ctx rule None anno [c])
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
             (* Out of scope: PP's EQS2 discharges ¬eql_set(E,F) by *disregarding*
                the marker's proof (spec §10.4.3 "ne pas tenir compte de la preuve")
                — it is sound only by the Set Translator's construction (E, F both
                simple variables standing for an equality that held at translation),
                so the equality is never recorded in the replay.  A trust-free
                reconstruction needs explicit eql_set evidence; the searches above
                cover every form we can recover it from.  When none matches the
                evidence is genuinely absent from the sequent, so we stop here with
                a diagnostic rather than guess. *)
             Errors.fail "E_EMIT"
               "EQS2: no eql_set(%s, %s) evidence in scope (PP disregards the \
                marker's proof, spec \xc2\xa710.4.3) \xe2\x80\x94 out of scope"
               (Emit_pp.prd_to_pp (Lift e)) (Emit_pp.prd_to_pp (Lift f))))
     | _ -> default ctx rule None anno [c])
  | P.Apply { rule; arg; anno; children = ([_; c1] as children); _ }
    when base rule = "AND4" ->
    (* Set-equality `E = F` proven directly: PP splits it into the two inclusions
       (sibling subgoals, the `⋀ ps` slot) plus an `eql_set` marker discharged by
       a STOP→EQS2 it skips.  There's no assumed evidence to feed EQS2, so instead
       reuse the inclusions: bind the `⋀ ps` proof once and assemble the marker
       from it via [eql_set_of_incls].  Falls back to the normal AND4 emit when the
       goal isn't this shape (the old EQS2 store-evidence path still applies). *)
    (match eqs2_marker_reuse ctx anno c1 with
     | Some t -> t
     | None -> default ctx rule arg anno children)
  | P.Apply { rule; anno; children = [c0; c1]; _ }
    when Rule_db.is_branching (base rule) ->
    branching ctx rule anno c0 c1
  | P.Apply { rule; arg; anno; children; _ } ->
    default ctx rule arg anno children

(* AND4 over a set-equality `E = F`: goal `⋀(∎ ∷ inclA ∷ inclB ∷ eql_set E F)`,
   where inclA/inclB are the two inclusion universals (`∀v. v ∈ X ⇒ v ∈ Y`).  PP
   proves both inclusions in the `⋀ ps` slot ([c1]) and skips the marker via EQS2;
   we instead bind that proof and build the marker from it with [eql_set_of_incls].
   Returns the assembled term, or None when the goal isn't this shape (e.g. the
   inclusion direction can't be matched), leaving the caller to fall back. *)
and eqs2_marker_reuse ctx anno c1 : L.t option =
  (* the marker `_eql_set(E,F)` parses as the pair-membership `(E,F) ϵ _eql_set` *)
  let marker_sides = function
    | Mem ([ e_exp; f_exp ], Var ("_eql_set" | "eql_set")) -> Some (e_exp, f_exp)
    | Lift (App (("_eql_set" | "eql_set"), [ e_exp; f_exp ])) -> Some (e_exp, f_exp)
    | _ -> None
  in
  match goal_of_anno anno with
  | Some g ->
    let conjs = Pp_lp.conj_children_left g in
    (match List.rev conjs, conjs with
     | marker :: _, incl0 :: incl1 :: _
       when List.length conjs = 3 && marker_sides marker <> None
            && (let (e, f) = Option.get (marker_sides marker) in
                not (exp_has_arith e) && not (exp_has_arith f)) ->
       let e_exp, f_exp = Option.get (marker_sides marker) in
       (* `!v. _ ⇒ (v ∈ X)` has consequent-membership target X *)
       let con_target = function
         | Bind ((Bang | Forall), [ v ], Binary (Imp, _, Mem ([ Var v' ], x)))
           when v' = v -> Some x
         | _ -> None
       in
       (* projections of pf : π (⋀ (∎ ∷ incl0 ∷ incl1)) *)
       let pf = L.Name "pf" in
       let last t = L.App (L.Name "\xe2\x8b\x80_last", [ t ]) in
       let init t = L.App (L.Name "\xe2\x8b\x80_init", [ t ]) in
       let p0 = last (init pf) and p1 = last pf in
       (* assign (hEF, hFE): E⊆F's consequent is `v ∈ F`, F⊆E's is `v ∈ E` *)
       let assignment =
         match con_target incl0, con_target incl1 with
         | Some t, _ when t = e_exp -> Some (p1, p0)
         | Some t, _ when t = f_exp -> Some (p0, p1)
         | _, Some t when t = e_exp -> Some (p0, p1)
         | _, Some t when t = f_exp -> Some (p1, p0)
         | _ -> None
       in
       Option.map
         (fun (h_ef, h_fe) ->
            let marker =
              L.App (L.Name "eql_set_of_incls",
                [ exp_term ctx e_exp; exp_term ctx f_exp; h_ef; h_fe ]) in
            let lam =
              L.Lambda ("pf", None, L.App (L.Name "AND4", [ marker; pf ])) in
            L.Then (L.Refine (lam, [ L.Hole ]),
                    scoped_hyps ctx (fun () -> tree ctx c1)))
         assignment
     | _ -> None)
  | None -> None

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
  | [], Rule_db.Opr rtl ->
    (* Terminal OPR (no continuation in the replay): PP's rewrite x ↦ E lands on a
       goal it discharges in one step — a bool-literal disequality.  Rewrite as
       usual, then close the residual `P[x ↦ E]` with [bool_diseq_closer].  Fail
       loud (never trust) if that residual isn't a closable bool disequality — the
       missing child is then a genuine REPLAY truncation. *)
    let eq_pred, residual =
      match goal with
      | Some (Binary (Imp, (Eq (l, r) as eq), body)) ->
        let e_val, x_side = if rtl then l, r else r, l in
        let res = match x_side with
          | Var x -> subst_prd [ (x, e_val) ] body
          | _ -> body in
        eq, res
      | _ -> failwith (Printf.sprintf
          "translate: terminal %s expected an `(x = E) ⇒ P` annotation" rule)
    in
    (match bool_diseq_closer residual with
     | Some closer ->
       let h = fresh_h ctx eq_pred in
       L.Assume (h,
         L.Then (L.Rewrite { try_ = true; rtl; name = h },
                 L.Step (L.Refine (closer, []))))
     | None -> failwith (Printf.sprintf
         "translate: terminal %s — residual goal is not a closable bool \
          disequality (likely a REPLAY truncation); refusing to emit trust" rule))
  | [], Rule_db.Default when base rule = "EVR3" ->
    (* Terminal EVR3: `(E = E) ⇒ P` with no continuation — the trivial reflexive
       antecedent and a one-step bool close.  EVR3 : π P → π ((E = E) ⇒ P); supply
       the closer for the consequent disequality P directly.  Fail loud otherwise. *)
    (match goal with
     | Some (Binary (Imp, _, p)) ->
       (match bool_diseq_closer p with
        | Some closer -> L.Step (L.Refine (L.Name "EVR3", [ closer ]))
        | None -> failwith
            "translate: terminal EVR3 — consequent is not a closable bool \
             disequality (likely a REPLAY truncation); refusing to emit trust")
     | _ -> failwith "translate: terminal EVR3 expected an `(E = E) ⇒ P` annotation")
  | [c], Rule_db.Ar3 ->
    (* Main-tree AR3.  PP's solver records the sub-premise `𝟏 - a` in its own
       normalised order `r` (the PipeArg's 2nd component), so the continuation is
       typed at `leq r 𝟎`.  Emit `AR3 a r <𝟏-a = r proof> _`; the equality is
       *generated* by [prove_sum_eq] (eq_refl-cheap when r = 𝟏 - a, so this single
       form subsumes the old plain/bridged split).  Fail loud (never trust) if the
       goal/arg shape is off or the equality can't be built. *)
    let env = proj_env_of_ctx ctx in
    let tactic =
      match goal, arg with
      | Some (Binary (Imp, Unary (Not, Leq (a_exp, Lit "0")), _)), Some (PipeArg (_, r_exp)) ->
        (match Arith_proofs.prove_sum_eq env (AOp (Sub, Lit "1", a_exp)) r_exp with
         | Some eqpf ->
           L.Refine (L.Name "AR3",
             [L.Exp (env, a_exp); L.Exp (env, r_exp); eqpf; L.Hole])
         | None -> failwith "translate: AR3 — couldn't build the `𝟏 - a = r` \
                             equality (prove_sum_eq), refusing to emit trust")
      | _ -> failwith "translate: AR3 — expected a `¬(leq a 𝟎) ⇒ R` goal with an \
                       `a | r` PipeArg, refusing to emit trust"
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
          (ar3f_cong ctx (proj_env_of_ctx ctx) [] g a_exp r_exp)
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
       Errors.fail "E_DISPATCH"
         "translate: %s trust-free dispatch unsupported — no corpus trace \
          exercises it (only NRM29 is wired)" other)
  | [c], Rule_db.Ar7_8 ->
    (* AR7/AR8.  The child IMP4 introduces the solver antisymmetry equality,
       recorded bare-variable-first (`b = a`); its sides give a (= rhs) and
       b (= lhs).  AR7's bound hyp is `(c+b) = (b−a) ≤ 𝟎`, AR8's is `(a−b) ≤ 𝟎`
       — recover it from scope (directly or term-reordered) as a real proof via
       [leaf_evidence]; the solver fact `a+c = 𝟎` is generated, no trust.  a/b/c are
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
          (leaf_evidence ctx [] (Leq (hyp_lhs, Lit "0")))
      | _ -> None
    in
    (match hbound_and_val with
     | Some (hb, value) ->
       (* The solver fact `(a + c) = 𝟎` is a cancellation (a = `rhs_e`, the
          antisymmetry RHS; c = —a) — [prove_sum_zero], no trust.  For AR7 c is
          the explicit value `—rhs_e`; for AR8 c is *goal-inferred* (the left
          summand of the goal antecedent `c + b`, b = lhs_e), so read it from
          there or the distributed form won't unify with `—rhs_e`.  Fail (never
          trust) if the shape is off. *)
       let acc_eq =
         let env = proj_env_of_ctx ctx in
         match goal_of_anno (P.anno_of c) with
         | Some (Binary (Imp, Eq (lhs_e, rhs_e), _)) ->
           let ac =
             if is_ar7 then Some (AOp (Add, rhs_e, Neg rhs_e))
             else
               (match goal_of_anno anno with
                | Some (Binary (Imp, Leq (AOp (Add, c_e, b_e), Lit "0"), _))
                  when b_e = lhs_e -> Some (AOp (Add, rhs_e, c_e))
                | _ -> None)
           in
           (match ac with
            | Some ac ->
              (match Arith_proofs.prove_sum_zero env ac with
               | Some t -> t
               | None -> failwith "translate: AR7/AR8 chain — prove_sum_zero \
                                   failed for the `(a+c)=𝟎` cancellation, \
                                   refusing to emit trust")
            | None -> failwith "translate: AR7/AR8 chain — unexpected goal shape \
                                for the `(a+c)=𝟎` cancellation, refusing to emit trust")
         | _ -> failwith "translate: AR7/AR8 chain — child annotation isn't the \
                          expected `E = F ⇒ …` equality, refusing to emit trust"
       in
       (* `hai hbi hci` (a/b/c ϵ INT) for the new guarded AR7/AR8: a = rhs_e,
          b = lhs_e; c = —a (AR7) or the goal's left summand `c + b` (AR8). *)
       let int_args =
         let env = proj_env_of_ctx ctx in
         match goal_of_anno (P.anno_of c) with
         | Some (Binary (Imp, Eq (lhs_e, rhs_e), _)) ->
           let c_exp =
             if is_ar7 then Neg rhs_e
             else (match goal_of_anno anno with
                   | Some (Binary (Imp, Leq (AOp (Add, c_e, _), Lit "0"), _)) -> c_e
                   | _ -> Neg rhs_e)
           in
           [ Arith_proofs.int_evidence env rhs_e; Arith_proofs.int_evidence env lhs_e;
             Arith_proofs.int_evidence env c_exp ]
         | _ -> [ L.Hole; L.Hole; L.Hole ]
       in
       let tactic =
         L.Refine (L.Name (base rule), value :: int_args @ [hb; acc_eq; L.Hole]) in
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
      Errors.fail "E_DISPATCH"
        "translate: %s arity %d unsupported"
        rule (List.length children)

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
  (* The continuation goal is `(!! v, res_tm (ρ v)) ⇒ R`.  When the chain result
     is itself a (nested) quantifier, that antecedent renders nested (`!! w, !! y,
     …`) — flatten_binds only ever merged *goal-level* binders, never one born
     inside a `res_tm`.  [tree] emits the §A.7–8 merge for real there (`refine
     ALL3/XST4/… _`, P inferred from the curried pattern conclusion), peeling one
     `Tuple n × Tuple 1 → Tuple (n+1)` level per node down to the ALL7/XST8 it then
     consumes — the same path it now takes for every main-tree merge. *)
  let cont_proof = scoped_hyps ctx (fun () -> tree ctx cont) in
  L.Then (tactic, cont_proof)

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
  | P.Apply { rule; anno; _ } when base rule = "NRM19" ->
    (* Chain-form NRM19 (Witness_hyp discharge).  NRM19_1 wraps `NRM19 v hr` in
       `mk_0 ∘ prop_eq_top` (a Res seed); PP's ⊤/VR4 child carries no premise so
       it's dropped.  Two evidence shapes:
        1. a real in-scope hyp `R v` ([find_nrm19_match], as the base rule does);
        2. a *reflexive self-pin* `forall2(x)·¬(⊤ ∧ (x = E)) ⇒ _`: the single
           binder is pinned to E, witnessed by `unit ⨾ E` with `R (unit⨾E)`
           reducing to `E = E`, discharged by `eq_refl E`.  (The witness E is the
           equality's constant side, which `ctx.xs` can't supply.) *)
    (match goal_of_anno anno with
     | Some goal ->
       (match find_nrm19_match ctx goal with
        | Some (witness, h) ->
          L.App (L.Name (chain_emit_name rule), [witness; L.Name h])
        | None ->
          let pin =
            match goal with
            | Binary (Imp, Bind (Forall2, [x],
                        Unary (Not, Binary (And, t, eqp))), _)
              when is_true_atom t ->
              (match eqp with
               | Eq (Var x', e) when x' = x -> Some e
               | Eq (e, Var x') when x' = x -> Some e
               | _ -> None)
            | _ -> None
          in
          (match pin with
           | Some e ->
             let et = exp_term ctx e in
             L.App (L.Name (chain_emit_name rule),
               [ L.App (L.Name "⨾", [L.Name "unit"; et]);
                 L.App (L.Name "eq_refl", [et]) ])
           | None ->
             failwith "translate: NRM19_1 — no in-scope hyp `R v` and not a \
                       reflexive single-binder pin `x = E`"))
     | None -> failwith "translate: NRM19_1 expected an implication annotation")
  | P.Apply { rule; anno; children = []; _ }
    when (match base rule with
          | "AXM1" | "AXM2" | "AXM3" | "AXM4" | "AXM5" | "AXM6" -> true
          | _ -> false) ->
    (* Chain-form AXM1-6 (Schema 0): the `_1` lemma needs the same hyp the
       base rule looks up.  Recover it from scope as a real proof term
       ([leaf_evidence] also bridges arith-reorder / equality-store shapes);
       the LP lemma reuses the base rule + `prop_eq_top`.  No hyp recovered ⇒
       fail (never trust). *)
    let no_ev () =
      failwith (Printf.sprintf
        "translate: chain-form %s — the hypothesis it needs isn't recoverable \
         from scope, refusing to emit trust" rule)
    in
    let ev =
      match goal_of_anno anno with
      | Some goal ->
        (match expected_hyp_pred rule goal with
         | Some needed ->
           (match leaf_evidence ctx [] needed with Some t -> t | None -> no_ev ())
         | None -> no_ev ())
      | None -> no_ev ()
    in
    L.App (L.Name (chain_emit_name rule), [ev])
  | P.Apply { rule; anno; children = []; _ } when base rule = "AXM8" ->
    (* Chain-form AXM8: the conjunct-extraction `π C → π r` the base rule
       builds, handed to AXM8_1 (which wraps it in `mk_0 ∘ prop_eq_top`). *)
    let f =
      match axm8_extraction ctx anno with
      | Some t -> t
      | None -> failwith "translate: chain-form AXM8 — couldn't extract the \
                          conjunct evidence, refusing to emit trust"
    in
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
  | P.Apply { rule; arg; anno; children = [c]; _ }
    when Rule_db.emit rule = Rule_db.Ar10 ->
    (* AR10_1 [P Q R] (P = Q) (Res (Q ⇒ R)) : Res (P ⇒ R).  Like the main-tree
       AR10: when P ≡ Q (identity solver) the continuation chain already has the
       result type, so skip the wrapper.  When PP's Q diverges from the goal
       antecedent P (real arithmetic normalisation), wrap the chain in `AR10_1
       <P = Q>` with the [prove_pred_eq] proof; fall back to the bare skip
       (warning) when that helper can't bridge the shape. *)
    (match goal_of_anno anno, arg_prd arg with
     | Some (Binary (Imp, p, _)), Some q when p <> q ->
       (match Arith_proofs.prove_pred_eq (proj_env_of_ctx ctx) p q with
        | Some pf -> app (chain_emit_name rule) [pf; chain_term ctx c]
        | None ->
          Errors.warn
            "AR10 (chain) skipped as a no-op, but its solver result Q differs \
             from the goal antecedent P (P = %s ; Q = %s)"
            (Emit_pp.prd_to_pp p) (Emit_pp.prd_to_pp q);
          chain_term ctx c)
     | _ -> chain_term ctx c)
  | P.Apply { rule; arg; anno; children = [c]; _ }
    when Rule_db.emit rule = Rule_db.Ar9 ->
    (* AR9_1 (F) (he : E = F) (r : Res ((F ≤ 𝟎) ⇒ R)) : Res ((E ≤ 𝟎) ⇒ R).  `he`
       is proved reflectively ([prove_sum_eq]) — `eq_refl` when E ≡ F (the corpus
       norm), the reflective normaliser when F reorders E.  Mirrors the main-tree
       AR9 dispatch; falls back to the bare `eq_refl` on an unexpected goal/arg
       shape (never `trust`). *)
    let env = proj_env_of_ctx ctx in
    let reflective =
      match goal_of_anno anno, arg with
      | Some (Binary (Imp, Leq (e_exp, Lit "0"), _)), Some (ExpArg f_exp) ->
        Option.map
          (fun eqpf -> app (chain_emit_name rule)
             [L.Exp (env, f_exp); eqpf; chain_term ctx c])
          (Arith_proofs.prove_sum_eq env e_exp f_exp)
      | _ -> None
    in
    (match reflective with
     | Some t -> t
     | None ->
       match dynamic_value_args ctx rule arg with
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
    (* AR3 in a Res chain.  PP's solver records the sub-premise `𝟏 - a` in its own
       normalised order `r` (the arg), so the continuation is typed at `leq r 𝟎`.
       Emit `AR3_1 a r <𝟏-a = r proof> cont`: `a` from the goal `¬(a≤𝟎) ⇒ R`, `r`
       from the arg, the equality *generated* by [prove_sum_eq] (no `trust`).  Fail
       loud if the shape is off or the equality can't be built. *)
    let env = proj_env_of_ctx ctx in
    (match goal_of_anno anno, arg with
     | Some (Binary (Imp, Unary (Not, Leq (a_exp, Lit "0")), _)), Some (PipeArg (_, r_exp)) ->
       (match Arith_proofs.prove_sum_eq env (AOp (Sub, Lit "1", a_exp)) r_exp with
        | Some eqpf ->
          L.App (L.Name "AR3_1",
            [L.Exp (env, a_exp); L.Exp (env, r_exp); eqpf; chain_term ctx c])
        | None -> failwith "translate: chain AR3 — couldn't build the `𝟏 - a = r` \
                            equality (prove_sum_eq), refusing to emit trust")
     | _ -> failwith "translate: chain AR3 — expected a `¬(leq a 𝟎) ⇒ R` goal with \
                      an `a | r` PipeArg, refusing to emit trust")
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
          let hyps =
            String.concat "\n"
              (List.map (fun (n, q) ->
                 Printf.sprintf "    %s : %s" n (Emit_pp.prd_to_pp q))
                 ctx.hyps)
          in
          failwith (Printf.sprintf
            "translate: IMP5_1 — the known-antecedent hyp is not in \
             scope\n  antecedent P: %s\n  hyps in scope (%d):\n%s"
            (Emit_pp.prd_to_pp p) (List.length ctx.hyps) hyps))
     | _ ->
       failwith "translate: IMP5_1 expected an implication annotation")
  | P.Apply { rule; anno; children = [c]; _ }
    when base rule = "NRM2" ->
    (* NRM2_1 (hp : π P) (r : Res ((♢v, Q v) ⇒ S)) : Res ((♢v, P ⇒ Q v) ⇒ S).
       PP's chain NRM2 weakens the ♢-body by its *v-free* antecedent P; that is
       sound only with a proof of P, so recover one from scope — the same leaf
       search the AXM chain forms use — and pass it as the first argument. *)
    (match goal_of_anno anno with
     | Some (Binary (Imp, Bind (_, _, Binary (Imp, p, _)), _)) ->
       (match leaf_evidence ctx [] p with
        | Some hp ->
          L.App (L.Name (chain_emit_name rule), [hp; chain_term ctx c])
        | None ->
          Errors.fail "E_EMIT"
            "NRM2_1: no in-scope evidence for the v-free ♢-body hypothesis")
     | _ ->
       Errors.fail "E_EMIT"
         "NRM2_1: expected a (♢v, P ⇒ Q v) ⇒ S chain annotation")
  | P.Apply { rule; _ }
    when base rule = "NRM20" ->
    (* NRM20 in a Res chain has no SOUND encoding: a `NRM20_1` would lean on the
       unproved `nrm20_eq` substitution bridge (a postulate).  Refuse rather than
       trust — these benchmarks time out on check regardless, so this costs no
       reconstructed goals while keeping the chain trust-free. *)
    Errors.fail "E_DISPATCH"
      "NRM20 appears in a result chain but has no trust-free encoding (the \
       nrm20_eq substitution bridge is unproved); refusing to emit a postulate"
  (* Chain-form binder merges (`[XST4_1]`, `[ALL3_1]`, …) and the De Morgan
     `[ALL5_1]` are NOT special-cased: they fall through to the generic
     single-child chain case below, which emits `<NAME>_1 child` (n/P/R inferred
     from the now-nested result type — flatten_binds is gone).  Their `_1` lemmas
     are in rules/All.lp, rules/Xst.lp; ALL5_1 transports the classical
     equivalence `all5_eq` (not a §A.7–8 congruence). *)
  | P.Apply { rule; anno; children = [c]; _ }
    when base rule = "IMP4"
         && (match goal_of_anno anno with
             | Some (Binary (Imp, ant, _)) ->
               chain_looks_up c ant && find_hyp_by_pred ctx ant = None
             | _ -> false) ->
    (* Chain `IMP4_1` whose child looks up the antecedent (the spec's IMP4'
       mounts P into H; a chain-local AXM3_1 then discharges a conjunct equal
       to it).  Bind the antecedent as a hypothesis, emit the child under it
       (the AXM's existing `leaf_evidence` search now finds it), and package as
       `IMP4_1U (λ hp, res_eq child)` — the result is unchanged, but the AXM is
       trust-free.  R (the child result) is inferred. *)
    (match goal_of_anno anno with
     | Some (Binary (Imp, ant, _)) ->
       ctx.n <- ctx.n + 1;
       let hp = Printf.sprintf "_h%d" ctx.n in
       let body =
         scoped_hyps ctx (fun () ->
           ctx.hyps <- (hp, ant) :: ctx.hyps;
           L.App (L.Name "res_eq", [chain_term ctx c]))
       in
       L.App (L.Name "IMP4_1U", [L.Lambda (hp, None, body)])
     | _ -> assert false)
  | P.Apply { rule; arg; anno; children = [c]; _ }
    when Rule_db.emit rule = Rule_db.Ar3_f ->
    (* AR3_F in a Res chain.  Like the main-tree AR3_F (see [tree_dispatch]): PP's
       forward normalisation rewrites the `¬(a ≤ 𝟎)` occurrence to `r ≤ 𝟎` in
       place.  Build the congruence `goal = goal'` for that exact (binder-nested)
       position and transport the child sub-chain — typed at the normalised
       `goal'` — back to `goal` with [res_cong] (`a = b → Res b → Res a`).
       `(a, r)` from the PipeArg.  Falls back to the bare child chain when the
       occurrence isn't on a supported path; that fails loud at the lambdapi
       check rather than emitting trust (and was previously the `AR3_F` unknown
       symbol the generic path emitted). *)
    let env = proj_env_of_ctx ctx in
    (match goal_of_anno anno, arg with
     | Some g, Some (PipeArg (a_exp, r_exp)) ->
       (match ar3f_cong ctx env [] g a_exp r_exp with
        | Some cong -> L.App (L.Name "res_cong", [cong; chain_term ctx c])
        | None -> chain_term ctx c)
     | _ -> chain_term ctx c)
  | P.Apply { rule; arg; children = [c]; _ } ->
    (* Mirror the main-tree arg bundle: dynamic value args, then the solver
       side-condition metadata (AR9's `E = F` equality, as `eq_refl`), then slot
       holes.  The chain path used to drop the metadata, so AR9_1 emitted without
       that equality and left the `he` goal unfilled ("missing subproofs"). *)
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
    Errors.fail "E_DISPATCH"
      "translate: chain %s arity %d unsupported"
      rule (List.length children)

let translate (pp_tree : P.pp_tree) : L.t =
  let ctx = create_ctx () in
  (* [Arith_proofs.int_evidence] resolves atomic `ϵ INT` evidence through this
     ref; bind it to this emission's ctx (single-threaded). *)
  Arith_proofs.atom_int_ev := atom_int_evidence ctx;
  tree ctx pp_tree
