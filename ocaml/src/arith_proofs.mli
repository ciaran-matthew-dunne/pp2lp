(* Arithmetic proof synthesis — the ctx-free solver bridge split out of
   [Emit_ctx] (move-only).  Operates on PP expressions / signed-atom lists and
   a projection env; never the mutable emission context.  The signed-atom
   normalisation, additive cancellation, and search internals are private. *)

open Syntax_pp

(* Flatten a `+`/`−` expression to its ordered signed-atom list (— pushed to the
   atoms); None if a non-arithmetic node blocks it.  The basis of [lin_normal]'s
   value comparison and of the witness/reorder searches in [Emit_ctx]. *)
val flatten_signed : exp -> (exp * int) list option

(* Left-nested sum of a signed-atom list, as a PP expression (`lfold [] ≡ 𝟎`). *)
val lfold_exp : (exp * int) list -> exp

(* `ϵ INT` evidence for a τ ι *atom* (a bound slot / free integer var): an
   injected typing premise.  Set once per emission by [Translate] to this run's
   ctx-side resolver ([Emit_ctx.atom_int_evidence]); the structural cases of
   [int_evidence] need no ctx, so it stays out of the public arith signatures. *)
val atom_int_ev : (exp -> Lp_tree.term) ref

(* `π (e ϵ INT)`: structural for compound terms / literals, else [atom_int_ev].
   The emitter supplies it to `int_retract` (the to_int-transport) and to the
   guarded arithmetic lemmas (AR5–8). *)
val int_evidence : Lp_tree.proj_env -> exp -> Lp_tree.term

(* `π (e1 = e2)` for two `+`/`−` expressions denoting the same value: the `e1=e2`
   fast path is `eq_refl`, otherwise the reflective normaliser ([reflect_eq]).
   None if either is non-linear or they differ.  Bridges arithmetic-reorder /
   normalisation gaps (INS conjuncts, AR3, Farkas) without `trust`. *)
val prove_sum_eq : Lp_tree.proj_env -> exp -> exp -> Lp_tree.term option

(* `π (e1 = e2)` for two τ ι expressions denoting the same value: structural
   congruence through the function-image / pair / `+`/`−`/neg constructors PP
   rewrites *through* (recursing on the differing child), then reflective ℤ-linear
   equality (commutation / reassociation / constant folding).  None when neither
   bridges the shape.  Exposed for the EGALITE hyp-match congruence bridge
   ([Emit_ctx.prove_prd_cong]), which closes the same leaves under binders. *)
val prove_exp_eq : Lp_tree.proj_env -> exp -> exp -> Lp_tree.term option

(* `π (p = q)` for two predicates differing only by arithmetic normalisation of
   their leaf expressions (AR10's `solveur(p) = q`): congruence down to the
   operands, each closed by [prove_exp_eq] (structural congruence through the
   function-image / pair / `+`/`−`/neg constructors PP rewrites *through*, then
   reflective ℤ-linear equality).  Handles the ¬/=/≤/ϵ shapes; None otherwise
   (the caller falls back to skipping the no-op). *)
val prove_pred_eq : Lp_tree.proj_env -> prd -> prd -> Lp_tree.term option

(* `π (e = 𝟎)` when [e]'s atoms cancel to nothing — `reflect_eq e (Lit "0")`.  Used
   by the trust-free NRM29 dispatch for the cancelling bounds. *)
val prove_sum_zero : Lp_tree.proj_env -> exp -> Lp_tree.term option

(* `π (e > 𝟎)` when [e] cancels/folds to a positive literal (AR4's `(E+F) > 𝟎`):
   transport [positive_lit] along the reflected `e = from_int c`. *)
val prove_gt_zero : Lp_tree.proj_env -> exp -> Lp_tree.term option

(* `π (¬ (from_int c ≤ 𝟎))` for a concrete positive literal c, passed as its
   decimal string (`one_not_leq_zero` for c = 1; magnitude-independent, so apero's
   2⁶⁴ bounds work).  [prove_gt_zero] transports it along `e = from_int c`; exposed
   for the Farkas certificate to refute its summed `c ≤ 𝟎`. *)
val positive_lit : Lp_tree.proj_env -> string -> Lp_tree.term

(* Farkas certificate for ⊥ from the `e ≤ 𝟎` hypotheses, found by Fourier–Motzkin
   elimination: a nonnegative integer combination of the hyps summing to a positive
   constant, emitted as a generated add_leq_zero / prove_sum_eq proof (no `trust`).
   Complete for ℚ-linear refutation — telescoping chains, sum-positivity and
   weighted sums alike — and returns None on a genuinely non-linear goal.  Takes the
   projection env and the candidate hyps as `(evidence, e, signed-atoms)`, where
   [evidence] is a `π (e ≤ 𝟎)` proof term (a bare hyp `Name h`, or a derived proof
   such as a discreteness-bridged `¬(e'≤𝟎)`); [Emit_ctx] supplies them from the
   context.  Returns the `π ⊥` proof term. *)
val find_arith_contradiction :
  Lp_tree.proj_env -> (Lp_tree.term * exp * (exp * int) list) list -> Lp_tree.term option

(* Prove `π (target ≤ 𝟎)` as a nonnegative integer combination of the `e ≤ 𝟎`
   hypotheses (the implied-bound dual of [find_arith_contradiction]).  Used by the
   INS search to discharge a universal's arithmetic gap conjunct.  Same hyp form
   (evidence term + e + signed-atoms); None when no nonnegative *integer*
   combination yields [target]. *)
val farkas_prove_leq :
  Lp_tree.proj_env -> (Lp_tree.term * exp * (exp * int) list) list -> exp ->
  Lp_tree.term option
