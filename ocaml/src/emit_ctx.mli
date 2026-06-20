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

(* `conj_prj_at var conjs k` — a proof of conjunct [k] (front-indexed) pulled
   from the n-element ⋀-list held by [var], via B.lp's back-indexed `conj_prj`.
   O(1) in the conjunct count (AXM8, AND5). *)
val conj_prj_at : Lp_tree.term -> prd list -> int -> Lp_tree.term

(* `and5_fwd var conjs ant_positions j` — the AND5 forward map `π C → π C'`:
   drop the implication conjunct [j] (`conj_rm`) and append its consequent,
   derived by applying [j] (`conj_prj`) to its antecedent at [ant_positions].
   O(1) in the conjunct count (the back-indexed combinators do the walking at
   reduction time). *)
val and5_fwd : Lp_tree.term -> prd list -> int list -> int -> Lp_tree.term

(* ---- Goal / annotation helpers ---- *)

val goal_of_anno : rhs option -> prd option
val binder_vars_of : prd -> string list option

(* True iff the predicate is the `⊤`/VRAI atom (e.g. the leading conjunct of a
   `¬(⊤ ∧ …)` normalisation body). *)
val is_true_atom : prd -> bool

(* The projection environment for the in-scope binders (each packed PP var →
   its `tuple ⋕ k` projection); a PP expression renders against it. *)
val proj_env_of_ctx : ctx -> Lp_tree.proj_env

(* The discharge term for a BOOL31/32/41/42 rule's `V ϵ BOOL` side-condition on
   var [v]: the typing oracle `trust_bool` applied to the atom in scope.  Total
   (always [Some _]); the option is kept for the caller's existing shape. *)
val bool_typing_term : ctx -> string -> Lp_tree.term option

(* The ctx-side atom resolver bound into [Arith_proofs.atom_int_ev] each
   emission: the typing oracle `trust_int` applied to the atom in scope. *)
val atom_int_evidence : ctx -> exp -> Lp_tree.term

(* ---- Searches over the context ---- *)

(* The hypothesis a [Hyp_search] rule (AXM1-6, EAXM1/2) needs, as a function
   of its goal; [find_hyp_by_pred] then locates it in scope by structural
   equality. *)
val expected_hyp_pred : string -> prd -> prd option
val find_hyp_by_pred : ctx -> prd -> string option

(* AR4: an in-scope `F ≤ 𝟎` hypothesis, returned as (F, its hyp name). *)
val find_leq_zero_hyp : ctx -> (exp * string) option

(* EQS2 store evidence for the `eql_set E F` marker: an assumed hyp that
   is `E = F` (returned with [true]; use via set_ext) or the marker
   itself (returned with [false]). *)
val find_eqs2_hyp : ctx -> exp -> exp -> (string * bool) option

(* EQS2 evidence from the refuted-inclusion universal pair
   (`forall2(x).not(x:E and not(x:F))` both ways). *)
val find_eqs2_incl_pair : ctx -> exp -> exp -> (string * string) option

(* EQS2 fallback: the marker as a (possibly nested) conjunct of an
   antecedent in R's implication spine — (antecedents before it, the
   ⋀-projection path: one (conjunct count, index) step per level). *)
val find_eqs2_spine : exp -> exp -> prd -> (int * (int * int) list) option

(* ECTR3/4: from the negated goal atom, an (equality hyp × substituted
   hyp) pair — (rewritten sub-expression E, equality hyp, swapped = ECTR4, hyp). *)
val find_ectr34 : ctx -> prd -> (exp * string * bool * string) option

(* ECTR1/2: from the equality antecedent (a, b), a (¬-hyp × substituted
   hyp) pair — (E-var, Q's body, ¬-hyp, F-hyp, swapped = ECTR2). *)
val find_ectr12 : ctx -> exp -> exp -> (string * prd * string * string * bool) option

(* ECTR5/6: from the positive antecedent, an (equality hyp × ¬-hyp) pair
   — (E-var, equality hyp, ¬-hyp, swapped = ECTR6). *)
val find_ectr56 : ctx -> prd -> (string * string * string * bool) option

(* The sum-equality / sum-zero / positivity provers (now reflective) live in
   [Arith_proofs] (ctx-free); the emitter calls them directly.  Their results are
   pure proof TERMS, so they also sit inside under-binder `!!_cong (λ v, …)` terms
   with no `have`/Π-quantification.  [find_arith_contradiction] below stays as a
   thin ctx wrapper over the Farkas search there. *)

(* Proof of a single `≤ 𝟎` (or ⊤) leaf from the in-scope hyps: a direct
   match (up to alpha / binder-kind) or, failing that, an arithmetic-reorder
   bridge (`prove_sum_eq` + `leq_subst_l`).  [None] if no hyp covers it.
   Used by the INS conjunct search and AR7/AR8's bound-inequality recovery. *)
val leaf_evidence : ctx -> (string * exp) list -> prd -> Lp_tree.term option

(* NRM29 trust-free dispatch.  Given the (post-AR3_F) goal
   `(♡(d,rest…)·¬⋀(cancelling-bounds)) ⇒ R`, returns `(b, cong)`: the witness
   `λ v', <w>` pinning the leading binder and the congruence proof
   `((♢v'·¬⋀ subst) ⇒ R) = ((♢v'·¬⊤) ⇒ R)` that ⊤-normalises the literal
   substituted conjunction (the caller transports with `=⇒ (eq_sym cong)`).
   None if the goal isn't the cancelling-bounds shape. *)
val nrm29_witness_bridge : ctx -> prd -> (Lp_tree.term * Lp_tree.term) option

(* AXM9 / NRM19: a (witness term, hyp name) discharging the goal. *)
val find_axm9_match : ctx -> prd -> (Lp_tree.term * string) option
val find_nrm19_match : ctx -> prd -> (Lp_tree.term * string) option

(* INS: the universal-instantiation contradiction, as a tactic *script* proving
   `π ⊥` — derived facts as named `have`s, existential raises as
   `refine … ; assume …` blocks, the close a `refine`.  [None] if no
   (universal hyp × witness) discharges the contradiction. *)
val find_ins_contradiction : ctx -> Lp_tree.t option

(* A human-readable diagnostic for when [find_ins_contradiction] returns
   [None]: the hypotheses and witnesses in scope, and per universal hyp the
   conjunct(s) that couldn't be discharged.  Used to build the INS failure
   message. *)
val ins_diagnostic : ctx -> string

(* ARITH: a Farkas-style certificate for ⊥ from the in-scope `e ≤ 𝟎` hyps —
   small nonnegative multipliers summing the hypotheses to 𝟏, emitted as a
   generated add_leq_zero / prove_sum_eq proof (no `trust`). *)
val find_arith_contradiction : ctx -> Lp_tree.tactic option
val arith_diagnostic : ctx -> string
