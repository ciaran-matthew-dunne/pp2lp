(* Arithmetic proof synthesis — the ctx-free solver bridge split out of
   [Emit_ctx] (move-only).  Operates on PP expressions / signed-atom lists and
   a projection env; never the mutable emission context.  The signed-atom
   normalisation, additive cancellation, and search internals are private. *)

open Syntax_pp

(* Flatten a `+`/`−` expression to its ordered signed-atom list (— pushed to
   the atoms; literals 2..64 unfolded to 𝟏-atoms); None if a non-arithmetic
   node blocks it.  Mirrors the internal [normalize]'s recursion. *)
val flatten_signed : exp -> (exp * int) list option

(* Left-nested sum of a signed-atom list, as a PP expression (`lfold [] ≡ 𝟎`). *)
val lfold_exp : (exp * int) list -> exp

(* `π (e1 = e2)` for two `+`/`−` expressions denoting the same signed-atom
   multiset after additive cancellation (`n + —n = 𝟎`); None if either is
   unsupported or the reduced multisets differ.  Bridges an arithmetic-reorder
   / normalisation gap (INS conjuncts, AR3_1) without `trust`. *)
val prove_sum_eq : Lp_tree.proj_env -> exp -> exp -> Lp_tree.term option

(* `π (e = 𝟎)` when [e]'s signed atoms cancel to the empty multiset (e.g.
   `—a + a`).  [prove_sum_eq … (Nat 0)] can't — `𝟎` is the atom `0`, not the
   empty list.  Used by the trust-free NRM29 dispatch for the cancelling bounds. *)
val prove_sum_zero : Lp_tree.proj_env -> exp -> Lp_tree.term option

(* `π (e > 𝟎)` when [e] cancels to a positive literal (AR4's `(E+F) > 𝟎`). *)
val prove_gt_zero : Lp_tree.proj_env -> exp -> Lp_tree.term option

(* Farkas-style certificate for ⊥ from the `e ≤ 𝟎` hypotheses: small
   nonnegative multipliers summing the hyps to 𝟏, emitted as a generated
   add_leq_zero / prove_sum_eq proof (no `trust`).  Takes the projection env
   and the candidate hyps as `(name, e, signed-atoms)`; [Emit_ctx] supplies
   them from the context. *)
val find_arith_contradiction :
  Lp_tree.proj_env -> (string * exp * (exp * int) list) list -> Lp_tree.tactic option
