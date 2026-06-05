(* Emission context and the lookups over it — the bottom layer of the
   emitter.  Exposes the mutable proof-construction state ([ctx]), the small
   goal/annotation helpers, the ⋀-list proof-term algebra, and the
   hypothesis / witness / INS searches.  The LP symbol vocabulary, the
   binder-insensitive predicate equality, and the search internals are
   private to this module. *)

open Syntax_pp

(* Translation context.  [n] is the fresh-name counter; [hyps] maps each
   `_hN` to the predicate it was introduced with (structural-equality hyp
   lookup); [xs] maps each `_xN` to the PP-side binder vars it stands for
   (witness substitution). *)
type ctx = {
  mutable n : int;
  mutable hyps : (string * prd) list;
  mutable xs : (string * string list) list;
}

val create_ctx : unit -> ctx

(* Allocate a fresh `_hN` / `_xN` and register it in the context.
   [fresh_x_local] allocates a `_xN` *without* registering — for a chain's
   `assume v`, scoped to the chain block and invisible to its sibling. *)
val fresh_h : ctx -> prd -> string
val fresh_x : ctx -> string list -> string
val fresh_x_local : ctx -> string

(* Run [f] with an extra `_xN`→pp-vars binding ([with_x]), or with hyp/var
   state saved and restored afterwards ([scoped_hyps]) — for branch arms. *)
val with_x : ctx -> string -> string list -> (unit -> 'a) -> 'a
val scoped_hyps : ctx -> (unit -> 'a) -> 'a

(* Rule-name helpers: [base] strips a `_1`/`_N` suffix; [chain_emit_name]
   primes an unprimed NRM rule for emission inside a Res chain. *)
val base : string -> string
val chain_emit_name : string -> string

(* ---- ⋀-list proof-term algebra (structured [Lp_tree.term]) ---- *)

(* `prj k t` — the k-th tuple projection of [t]. *)
val prj : int -> Lp_tree.term -> Lp_tree.term

(* `eq_refl t` — reflexivity proof of the equality term [t]. *)
val eq_refl : Lp_tree.term -> Lp_tree.term

(* `extract var conjs k` — a proof of conjunct [k] pulled from the n-element
   ⋀-list held by [var] (AXM8). *)
val extract : Lp_tree.term -> prd list -> int -> Lp_tree.term

(* `and5_fwd var conjs ant_positions j` — rebuild the ⋀-list with conjunct
   [j] (an implication) discharged by its antecedent at [ant_positions]. *)
val and5_fwd : Lp_tree.term -> prd list -> int list -> int -> Lp_tree.term

(* ---- Goal / annotation helpers ---- *)

val goal_of_anno : rhs option -> prd option
val binder_vars_of : prd -> string list option

(* ---- Searches over the context ---- *)

(* The hypothesis a [Hyp_search] rule (AXM1-6, EAXM1/2) needs, as a function
   of its goal; [find_hyp_by_pred] then locates it in scope by structural
   equality. *)
val expected_hyp_pred : string -> prd -> prd option
val find_hyp_by_pred : ctx -> prd -> string option

(* AR4: an in-scope `F ≤ 𝟎` hypothesis, returned as (F, its hyp name). *)
val find_leq_zero_hyp : ctx -> (exp * string) option

(* The tuple-projection env (witness var → `prj k x`) for rendering PP
   expressions; built from the in-scope binders.  Mirrors [Rule_emit.pp_env_of]. *)
val proj_env_of_ctx : ctx -> Lp_tree.proj_env

(* `π (e1 = e2)` for two `+`/`−` expressions denoting the same signed-atom
   multiset (— pushed to leaves), built from `add_comm`/`add_assoc`/`opp_add`/
   `neg_neg`; None if unsupported or the multisets differ.  Used to bridge an
   arithmetic-reorder/normalisation gap (INS conjuncts, AR3_1) without `trust`. *)
val prove_sum_eq : Lp_tree.proj_env -> exp -> exp -> Lp_tree.term option

(* Proof of a single `≤ 𝟎` (or ⊤) leaf from the in-scope hyps: a direct
   match (up to alpha / binder-kind) or, failing that, an arithmetic-reorder
   bridge (`prove_sum_eq` + `leq_subst_l`).  [None] if no hyp covers it.
   Used by the INS conjunct search and AR7/AR8's bound-inequality recovery. *)
val leaf_evidence : ctx -> (string * exp) list -> prd -> Lp_tree.term option

(* AXM9 / NRM19: a (witness term, hyp name) discharging the goal. *)
val find_axm9_match : ctx -> prd -> (Lp_tree.term * string) option
val find_nrm19_match : ctx -> prd -> (Lp_tree.term * string) option

(* INS: the `!!_to_pi …` contradiction tactic, if a universal hyp × witness
   pair matches every conjunct. *)
val find_ins_contradiction : ctx -> Lp_tree.tactic option

(* A human-readable diagnostic for when [find_ins_contradiction] returns
   [None]: the hypotheses and witnesses in scope, and per universal hyp the
   conjunct(s) that couldn't be discharged.  Used to build the INS failure
   message. *)
val ins_diagnostic : ctx -> string
