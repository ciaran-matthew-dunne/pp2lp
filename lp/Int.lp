// Int.lp — integer arithmetic for the shallow encoding, embedded from Stdlib.Z.
// `+`/`—`/`≤`/`𝟎`/`𝟏` are DEFINED via an injection `from_int : ℤ → τ ι`, so the
// discretely-ordered-abelian-group laws are *proved*, not postulated.
//
// This is the ONLY module that requires Stdlib.Z, which contains the numeral
// clash: Z and Nat both bind the bare literals `0..10`.  Z is required *last*
// here so this file's own bare numerals are ℤ; Nat's are restored at the end
// (see bottom) so downstream modules read bare numerals as ℕ (Tuple arities).
require open pp2lp.B;
require open Stdlib.Nat;
require Stdlib.Z as Z;
require Stdlib.Pos;

// ---- Arithmetic on τ ι (embedded from Stdlib.Z) ----
// +, —, ≤, 𝟎, 𝟏 are DEFINED via an injection from ℤ, so the discretely-ordered
// abelian-group laws are *proved* from Stdlib.Z rather than postulated.
// `from_int` injects ℤ; `to_int` is a left inverse; `INT` is the range of
// `from_int`.  The two laws that recover an element from its projection
// (add_zero, leq_antisym) hold only on INT and carry an `ϵ INT` premise, which
// the emitter supplies from inferred integer typing (cf. the BOOL premises).
type nat;
symbol NAT : τ ι;

symbol from_int : Z.ℤ → τ ι;
// `injective` is a unification hint (to_int is a left inverse of from_int): it
// lets lambdapi solve `to_int ?x ≡ to_int t` ⟹ `?x ≔ t`, which the defined `≤`/`+`
// otherwise hide.  It adds no provable axiom, so no soundness cost.
injective symbol to_int : τ ι → τ Z.int;
rule to_int (from_int $z) ↪ $z;

constant symbol INT : τ ι;
symbol int_mem (v : τ ι) : π ((v ϵ INT) ⇔ (`∃ z, v = from_int z));

// x ϵ INT gives the retraction from_int (to_int x) = x.
opaque symbol int_retract (x : τ ι) : π (x ϵ INT) → π (x = from_int (to_int x)) ≔
begin assume x hx; refine ∃ₑ (∧ₑ₁ (int_mem x) hx) (λ z hz, _); rewrite hz; reflexivity end;

// Everything in the range of from_int is in INT (the converse direction PP needs:
// literals and any `from_int`-built term discharge their `ϵ INT` side-conditions).
opaque symbol from_int_in_int (z : Z.ℤ) : π (from_int z ϵ INT) ≔
begin assume z; refine ∧ₑ₂ (int_mem (from_int z)) (∃ᵢ z (eq_refl (from_int z))) end;

// Constants
symbol 𝟎 ≔ from_int 0;
symbol 𝟏 ≔ from_int 1;

opaque symbol zero_in_int : π (𝟎 ϵ INT) ≔ from_int_in_int Z.Z0;

// Operations. Precedence chosen so `+/−` bind tighter than `≤/=`.
symbol + (x y : τ ι) : τ ι ≔ from_int (Z.+ (to_int x) (to_int y));
notation + infix left 20;

symbol — (x : τ ι) : τ ι ≔ from_int (Z.— (to_int x)); // unary minus
notation — prefix 25;

symbol - (x y : τ ι) ≔ x + (— y);
notation - infix left 20;

// Decimal literals: a numeral parses as ℤ (Stdlib.Z's builtin) and coerces into
// τ ι through the injection, so the emitter can write bare numerals where a τ ι
// value is expected.
coerce_rule coerce Z.ℤ (τ ι) $z ↪ from_int $z;

// Ordering.  `≤` is kept ABSTRACT (no definition) so unification treats it
// rigidly: an AR rule whose `(E ≤ E')` conclusion unifies against a concrete
// goal recovers the implicit operands by `injective` decomposition, instead of
// reducing through `Z.≤`/`isGt` and losing them (fatal for the reflexive
// `E ≤ E`, where `to_int ?E ≐ to_int ?E ↪ Eq` erases ?E).  Its meaning is the
// axiomatised equality `le_def`; `le_intro`/`le_elim` (proved from it, not
// axioms) bridge to `Stdlib.Z.≤` in the laws below, and the emitter `rewrite`s
// `le_def` only where it must genuinely compute `≤`.
injective symbol ≤ : τ ι → τ ι → Prop;
notation ≤ infix 5;

symbol le_def (x y : τ ι) : π ((x ≤ y) = (Z.≤ (to_int x) (to_int y)));

opaque symbol le_intro (x y : τ ι) : π (Z.≤ (to_int x) (to_int y)) → π (x ≤ y) ≔
begin assume x y h; refine =⇒ (eq_sym (le_def x y)) h end;
opaque symbol le_elim (x y : τ ι) : π (x ≤ y) → π (Z.≤ (to_int x) (to_int y)) ≔
begin assume x y h; refine =⇒ (le_def x y) h end;

symbol > ≔ λ x y, ¬ (x ≤ y);
notation > infix 5;

// ≪ is a PP-internal proof-search marker (prevents AR12 loops); semantically
// identical to ≤. PP never emits ≪ on the wire, so we alias it here so that
// rule signatures retaining ≪ (AR5–AR8, AR13) unify with PP's ≤ hypotheses.
symbol ≪ : τ ι → τ ι → Prop ≔ ≤;
notation ≪ infix 5;

// Compound terms are structurally in INT (— and + land in from_int's range),
// so their `ϵ INT` side-conditions discharge without an injected premise.
opaque symbol neg_in_int (a : τ ι) : π ((— a) ϵ INT) ≔ from_int_in_int (Z.— (to_int a));
opaque symbol add_in_int (a b : τ ι) : π ((a + b) ϵ INT) ≔ from_int_in_int (Z.+ (to_int a) (to_int b));

// ---- Z-level helpers (pure ℤ; the τ ι laws below `refine` these) ----
// Kept on ℤ so `rewrite` matches the `Z.+` subterms directly: unfolding the
// τ ι `≤` to its `… ⇒ ⊥` form (what `simplify` does) would defeat `rewrite`.

opaque symbol Z_add_leq_l (a b c : Z.ℤ) : π (Z.≤ a b) → π (Z.≤ (Z.+ c a) (Z.+ c b)) ≔
begin
  assume a b c h; rewrite Z.+_com c a; rewrite Z.+_com c b;
  refine Z.≤_compat_add a b c h
end;

opaque symbol Z_leq_succ (a : Z.ℤ) : π (Z.≤ a (Z.+ a 1)) ≔
begin
  assume a; have h01 : π (Z.≤ 0 1) { assume k; refine k };
  rewrite Z.+_com a 1; refine Z.≤_compat_add 0 1 a h01
end;

opaque symbol Z_sub_add (a b : Z.ℤ) : π (Z.+ (Z.+ a (Z.— b)) b = a) ≔
begin
  assume a b; rewrite Z.+_assoc a (Z.— b) b; rewrite Z.+_com (Z.— b) b;
  rewrite Z.-_same b; reflexivity
end;

opaque symbol Z_neg_add (b : Z.ℤ) : π (Z.+ (Z.— b) b = 0) ≔
begin assume b; rewrite Z.+_com (Z.— b) b; refine Z.-_same b end;

opaque symbol Z_sub_leq (a b : Z.ℤ) : π (Z.≤ a b) → π (Z.≤ (Z.+ a (Z.— b)) 0) ≔
begin assume a b h; rewrite left (Z.-_same b); refine Z.≤_compat_add a b (Z.— b) h end;

opaque symbol Z_leq_of_sub (a b : Z.ℤ) : π (Z.≤ (Z.+ a (Z.— b)) 0) → π (Z.≤ a b) ≔
begin assume a b h; rewrite left (Z_sub_add a b); refine Z.≤_compat_add (Z.+ a (Z.— b)) 0 b h end;

opaque symbol Z_neg_leq (a : Z.ℤ) : π (Z.≤ (Z.— a) 0) → π (Z.≤ 0 a) ≔
begin assume a h; rewrite left (Z_neg_add a); refine Z.≤_compat_add (Z.— a) 0 a h end;

// ---- Laws — discretely ordered abelian group on τ ι, proved from Stdlib.Z ----

opaque symbol leq_refl (x : τ ι) : π (x ≤ x) ≔
begin assume x; refine le_intro x x (Z.≤_refl (to_int x)) end;

opaque symbol leq_trans (x y z : τ ι) :
  π (x ≤ y) → π (y ≤ z) → π (x ≤ z) ≔
begin assume x y z h1 h2;
  refine le_intro x z (Z.≤_trans (to_int x) (to_int y) (to_int z)
    (le_elim x y h1) (le_elim y z h2)) end;

// Antisymmetry recovers an equality between the elements, so it needs both in INT.
opaque symbol leq_antisym (x y : τ ι) (hx : π (x ϵ INT)) (hy : π (y ϵ INT)) :
  π (x ≤ y) → π (y ≤ x) → π (x = y) ≔
begin
  assume x y hx hy hxy hyx;
  have h : π (to_int x = to_int y)
    { refine Z.≤_antisym (to_int x) (to_int y) (le_elim x y hxy) (le_elim y x hyx) };
  rewrite (int_retract x hx); rewrite (int_retract y hy); refine feq from_int h
end;

opaque symbol add_comm (x y : τ ι) : π (x + y = y + x) ≔
begin assume x y; refine feq from_int (Z.+_com (to_int x) (to_int y)) end;

opaque symbol add_assoc (x y z : τ ι) : π ((x + y) + z = x + (y + z)) ≔
begin assume x y z; refine feq from_int (Z.+_assoc (to_int x) (to_int y) (to_int z)) end;

// 𝟎 is the right identity only on INT (it recovers x); the emitter supplies `ϵ INT`.
opaque symbol add_zero (x : τ ι) (hx : π (x ϵ INT)) : π (x + 𝟎 = x) ≔
begin assume x hx; symmetry; refine int_retract x hx end;

opaque symbol add_neg (x : τ ι) : π (x + — x = 𝟎) ≔
begin assume x; refine feq from_int (Z.-_same (to_int x)) end;

// Translation invariance: x ≤ y → z + x ≤ z + y.
opaque symbol add_leq_l (x y z : τ ι) : π (x ≤ y) → π (z + x ≤ z + y) ≔
begin assume x y z h;
  refine le_intro (z + x) (z + y) (Z_add_leq_l (to_int x) (to_int y) (to_int z) (le_elim x y h)) end;

// 𝟏 is strictly positive; 𝟎 ≤ 𝟏 — both decided by the Z comparison.
opaque symbol one_not_leq_zero : π (¬ (𝟏 ≤ 𝟎)) ≔
begin assume h; refine (le_elim 𝟏 𝟎 h) ⊤ᵢ end;

opaque symbol zero_leq_one : π (𝟎 ≤ 𝟏) ≔
begin refine le_intro 𝟎 𝟏 _; assume h; refine h end;

// Discreteness: no integer strictly between 𝟎 and 𝟏.  `compare H p` is never Gt
// (Pos), so 𝟏 ≤ any positive; the 0/negative cases contradict ¬(x ≤ 𝟎).
opaque symbol one_le_pos (p : Stdlib.Pos.ℙ) : π (Z.≤ (Z.Zpos Stdlib.Pos.H) (Z.Zpos p)) ≔
begin
  induction
  { assume q ih k; refine k }
  { assume q ih k; refine k }
  { assume k; refine k }
end;

opaque symbol Z_discrete (z : Z.ℤ) : π (¬ (Z.≤ z 0)) → π (Z.≤ 1 z) ≔
begin
  induction
  { assume h; refine ⊥ₑ (h _); assume k; refine k }
  { assume p h; refine one_le_pos p }
  { assume p h; refine ⊥ₑ (h _); assume k; refine k }
end;

opaque symbol discrete (x : τ ι) : π (¬ (x ≤ 𝟎)) → π (𝟏 ≤ x) ≔
begin assume x h;
  refine le_intro 𝟏 x (Z_discrete (to_int x) (λ hz, h (le_intro x 𝟎 hz))) end;

// ---- Derived lemmas (left-/right- variants of the axioms) ----

// Congruences + ≤-transport used by the emitter's on-the-fly equality
// proofs: an INS conjunct (or AR3 sub-premise) PP records in a different
// term order than the rule/universal it feeds is bridged by a generated
// `add_comm`/`add_assoc`/`opp_add`/`neg_neg` permutation proof (no `trust`).
// Plain `rewrite` (not AC) so each step is predictable.
opaque symbol add_congL (b : τ ι) [a a' : τ ι] :
  π (a = a') → π (a + b = a' + b) ≔
begin assume b a a' h; rewrite h; reflexivity end;

opaque symbol add_congR (a : τ ι) [b b' : τ ι] :
  π (b = b') → π (a + b = a + b') ≔
begin assume a b b' h; rewrite h; reflexivity end;

opaque symbol add_cong [a a' b b' : τ ι] :
  π (a = a') → π (b = b') → π (a + b = a' + b') ≔
begin assume a a' b b' ha hb; rewrite ha; rewrite hb; reflexivity end;

opaque symbol leq_subst_l [a b : τ ι] :
  π (a = b) → π (b ≤ 𝟎) → π (a ≤ 𝟎) ≔
begin assume a b h hb; rewrite h; refine hb end;

opaque symbol zero_add (x : τ ι) (hx : π (x ϵ INT)) : π (𝟎 + x = x) ≔
begin assume x hx; symmetry; refine int_retract x hx end;

opaque symbol neg_add (x : τ ι) : π ((— x) + x = 𝟎) ≔
begin assume x; refine feq from_int (Z_neg_add (to_int x)) end;

opaque symbol add_leq_r (x y z : τ ι) :
  π (x ≤ y) → π (x + z ≤ y + z) ≔
begin assume x y z h;
  refine le_intro (x + z) (y + z) (Z.≤_compat_add (to_int x) (to_int y) (to_int z) (le_elim x y h)) end;

// x ≤ x + 𝟏.  The ARITH closer chains this to refute a positive-literal sum.
opaque symbol leq_plus_one (x : τ ι) : π (x ≤ x + 𝟏) ≔
begin assume x; refine le_intro x (x + 𝟏) (Z_leq_succ (to_int x)) end;

// Sum of two non-positives is non-positive.
opaque symbol add_leq_zero (x y : τ ι) :
  π (x ≤ 𝟎) → π (y ≤ 𝟎) → π (x + y ≤ 𝟎) ≔
begin
  assume x y hx hy;
  refine le_intro (x + y) 𝟎 _;
  refine Z.≤_trans (Z.+ (to_int x) (to_int y)) (to_int y) 0 _ (le_elim y 𝟎 hy);
  refine Z.≤_compat_add (to_int x) 0 (to_int y) (le_elim x 𝟎 hx)
end;

// Literal positivity for the AR2/AR4 closer.  `prove_gt_zero` must refute
// `c ≤ 𝟎` for a positive literal c; the unary chain (leq_plus_one × c) is
// O(c) and blows up past ~64 (apero hits MAXINT-scale 2³¹).  These give an
// O(1) witness for any magnitude, the literal staying folded (no diverging
// whnf): every nat-literal is ≥ 𝟎 (by ℕ-induction), and `𝟏 + (≥𝟎) > 𝟎`.
opaque symbol pos_add (x : τ ι) : π (𝟎 ≤ x) → π (¬ (𝟏 + x ≤ 𝟎)) ≔
begin
  assume x h hk;
  have h1 : π (Z.≤ 1 (Z.+ 1 (to_int x)))
    { rewrite Z.+_com 1 (to_int x); refine Z.≤_compat_add 0 (to_int x) 1 (le_elim 𝟎 x h) };
  refine (Z.≤_trans 1 (Z.+ 1 (to_int x)) 0 h1 (le_elim (𝟏 + x) 𝟎 hk)) ⊤ᵢ
end;

// A concrete positive literal `from_int (Zpos p)` is > 𝟎, for any magnitude p.
// `Zpos p ≐ Z0 ↪ Gt` by head match (p stays symbolic), so the `≤` reduces to
// `¬⊤` exactly as `one_not_leq_zero` (p = H) does — O(1), no unary blowup.
// The emitter's `prove_gt_zero` uses this past the 64-atom unfold cap.
opaque symbol lit_pos (p : Stdlib.Pos.ℙ) : π (¬ (from_int (Stdlib.Z.Zpos p) ≤ 𝟎)) ≔
begin assume p h; refine (le_elim (from_int (Stdlib.Z.Zpos p)) 𝟎 h) ⊤ᵢ end;

// x ≤ y ↔ x − y ≤ 𝟎 (sub_leq forward, leq_of_sub converse). Used by AR3, AR5–AR8, AR13.
opaque symbol sub_leq (x y : τ ι) : π (x ≤ y) → π (x - y ≤ 𝟎) ≔
begin assume x y h; refine le_intro (x - y) 𝟎 (Z_sub_leq (to_int x) (to_int y) (le_elim x y h)) end;

opaque symbol leq_of_sub (x y : τ ι) : π (x - y ≤ 𝟎) → π (x ≤ y) ≔
begin assume x y h; refine le_intro x y (Z_leq_of_sub (to_int x) (to_int y) (le_elim (x - y) 𝟎 h)) end;

// — flips ≤. Used by AR5, AR6.
opaque symbol neg_leq_zero (a : τ ι) : π (— a ≤ 𝟎) → π (𝟎 ≤ a) ≔
begin assume a h; refine le_intro 𝟎 a (Z_neg_leq (to_int a) (le_elim (— a) 𝟎 h)) end;

// ---- Algebraic identities (proved directly from Stdlib.Z) ----

// —𝟎 = 𝟎.
opaque symbol neg_zero : π (— 𝟎 = 𝟎) ≔
begin reflexivity end;

// — is involutive: —(—x) = x (recovers x, so guarded by `ϵ INT`).
opaque symbol neg_neg (x : τ ι) (hx : π (x ϵ INT)) : π (— (— x) = x) ≔
begin assume x hx; simplify; rewrite (Z.—_idem (to_int x)); symmetry; refine int_retract x hx end;

// Negation distributes over +: —(x + y) = (—x) + (—y).
opaque symbol opp_add (x y : τ ι) : π (— (x + y) = (— x) + (— y)) ≔
begin assume x y; refine feq from_int (Z.distr_—_+ (to_int x) (to_int y)) end;


// ---- Numeral builtins ----
// `require Stdlib.Z` above clobbered the shared "0".."10" decimal-literal keys
// (Stdlib.Z and Stdlib.Nat both register them), so B.lp's own bare numerals are
// ℤ.  Restore Stdlib.Nat's here so downstream modules (Quant, rules, bench) read
// bare numerals as ℕ — they use them only for `Tuple` arities; ℤ literals are
// always written explicitly (B.lp) or rendered via `from_int` (emitter).
builtin "0" ≔ _0; builtin "1" ≔ _1; builtin "2" ≔ _2; builtin "3" ≔ _3;
builtin "4" ≔ _4; builtin "5" ≔ _5; builtin "6" ≔ _6; builtin "7" ≔ _7;
builtin "8" ≔ _8; builtin "9" ≔ _9; builtin "10" ≔ _10;
// Multi-digit numerals expand positionally through the `"+"`/`"*"` builtins, so
// those must be Nat's too — otherwise `Tuple 10` parses as ℤ-`+`/`*` over ℕ
// digits and clashes (ℤ vs ℕ).  The digit re-registration above is not enough.
builtin "+" ≔ Stdlib.Nat.+; builtin "*" ≔ Stdlib.Nat.*;
