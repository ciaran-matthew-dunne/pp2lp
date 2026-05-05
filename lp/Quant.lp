// Tuple-based n-ary quantifier machinery — foundations.
//
// `!!` and `??` are n-ary universal/existential quantifiers
// indexed by a Tuple n. The substantive rules (ALL4, ALL5, ALL7,
// XST5, XST7, XST8, …) live in lp/rules/All.lp and lp/rules/Xst.lp;
// this file only exposes the kernel needed to state and use them.
//
//   Tuple n        : an n-tuple of τ ι values
//   prj k v        : k-th projection (counts from the right;
//                    prj 0 v is the most recently appended element,
//                    which corresponds to the *outermost* `!!` binder)
//   `!! v : Tuple n, P v
//                  : `∀ x_1 ... ∀ x_n, P (unit ⨾ x_1 ⨾ … ⨾ x_n)`
//                    declared `quantifier`, so the standard sugar
//                    works:  `!! v, body`  ≡  `!! (λ v, body)`
//   `?? v : Tuple n, P v
//                  : analogous, with ∃ at every layer.
//
// Bridges:
//   pi_to_!!  : (Π v, π (P v))         → π (`!! v, P v)   — intro
//   !!_to_pi  : π (`!! v, P v)         → Π v, π (P v)     — elim
//   pi_to_??_intro : Π v, π (P v) → π (`?? v, P v)        — intro
//   pi_to_??_elim  : (Π v, π (P v) → π R) → π (`?? v, P v) → π R
//                                                          — elim

require open pp2lp.B;

// ---- Tuple ------------------------------------------------------

inductive Tuple : ℕ → TYPE ≔
  | unit : Tuple 0
  | ⨾ [n] : Tuple n → τ ι → Tuple (+1 n);
notation ⨾ infix left 5;

// k-th projection. prj 0 picks the rightmost (most recently
// appended) element.
symbol prj [n] (k : ℕ) (_ : Tuple n) : τ ι;
rule prj (+1 $n) ($t ⨾ _) ↪ prj $n $t
with prj 0      (_ ⨾ $x) ↪ $x;

// Canonical inhabitant of `Tuple n` — every slot filled with `inh`.
// Used when a rule needs a witness tuple but its predicate is
// independent of the tuple's contents.
symbol inh_tuple [n] : Tuple n;
rule inh_tuple [0] ↪ unit
with inh_tuple [+1 $n] ↪ inh_tuple [$n] ⨾ inh;

// ---- `!!` n-ary universal --------------------------------------
//
// Kept *rigid* (no reduction rules). If `!!` reduced eagerly to
// nested ∀, the surface form would vanish from goals before any
// tactic could see it — and implicit-arg inference of `n` and `P`
// at call sites would need to invert the reduction (higher-order
// unification across rewriting), which Lambdapi can't.

constant symbol !! [n] : (Tuple n → Prop) → Prop;
notation !! quantifier;

constant symbol pi_to_!! [n] (P : Tuple n → Prop)
  : (Π v : Tuple n, π (P v)) → π (`!! v, P v);

constant symbol !!_to_pi [n] (P : Tuple n → Prop)
  : π (`!! v, P v) → Π v : Tuple n, π (P v);

// ---- `??` n-ary existential ------------------------------------
//
// Kept *rigid* like `!!`. Earlier we let `??` reduce to nested ∃,
// but that broke implicit-P inference at sites like XST7_1's body
// (HO-unification can't invert the reduction). Bridges are
// axiomatised below.

constant symbol ?? [n] : (Tuple n → Prop) → Prop;
notation ?? quantifier;

constant symbol pi_to_??_intro [n] (P : Tuple n → Prop)
  : Π v : Tuple n, π (P v) → π (`?? v, P v);

constant symbol pi_to_??_elim [n] (P : Tuple n → Prop) [R : Prop]
  : (Π v : Tuple n, π (P v) → π R) → π (`?? v, P v) → π R;

// ---- Common derived lemmas -------------------------------------

// Pointwise equality lifts to `!!` equality.
opaque symbol !!_cong [n] [P R : Tuple n → Prop]
  : (Π v : Tuple n, π (P v = R v))
  → π ((`!! v, P v) = (`!! v, R v)) ≔
begin
  assume n P R h;
  refine propExt _ _ _ _
  { assume hP; refine pi_to_!! R (λ v, =⇒ (h v) (!!_to_pi P hP v)) }
  { assume hR; refine pi_to_!! P (λ v, =⇒ (eq_sym (h v)) (!!_to_pi R hR v)) }
end;

// Pointwise equality lifts to `??` equality.
opaque symbol ??_cong [n] [P R : Tuple n → Prop]
  : (Π v : Tuple n, π (P v = R v))
  → π ((`?? v, P v) = (`?? v, R v)) ≔
begin
  assume n P R h;
  refine propExt _ _ _ _
  { assume hP; refine pi_to_??_elim P
      (λ v hPv, pi_to_??_intro R v (=⇒ (h v) hPv)) hP }
  { assume hR; refine pi_to_??_elim R
      (λ v hRv, pi_to_??_intro P v (=⇒ (eq_sym (h v)) hRv)) hR }
end;

// ---- Res: Σ-type for normalisation chains ----------------------
//
// `Res t = (t' : τ a) × π (t = t')` packages a normalised term with
// a proof of equality to the original.  Lives here (not in Res.lp)
// because the result-based ALL7/XST8 in All.lp/Xst.lp need it.

injective symbol Res [a : Set] : τ a → TYPE;
symbol mk_1 [a t] (t' : τ a) : π (t = t') → Res t;
sequential symbol res_tm [a t] : Res [a] t → τ a;
sequential symbol res_eq [a t] (r : Res [a] t) : π (t = res_tm r);
rule res_tm (mk_1 $t' _) ↪ $t';
rule res_eq (mk_1 _ $prf) ↪ $prf;
