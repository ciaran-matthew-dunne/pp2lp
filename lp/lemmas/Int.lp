// lemmas/Int.lp — the proved integer laws.
//
// Derived from B.lp's abstract plus/neg/leq, their def-axioms, and Stdlib.Z.
// The discretely-ordered-abelian-group laws are proofs, not postulates.
require open pp2lp.B;
require open Stdlib.Z;

// x ϵ INT gives the retraction from_int (to_int x) = x.
opaque symbol int_retract (x : τ ι) : π (x ϵ INT) → π (x = from_int (to_int x)) ≔
begin assume x hx; refine ∃ₑ (∧ₑ₁ (int_mem x) hx) (λ z hz, _); rewrite hz; reflexivity end;

// Range of from_int ⊆ INT: literals and from_int-built terms discharge `ϵ INT`.
opaque symbol from_int_in_int (z : ℤ) : π (from_int z ϵ INT) ≔
begin assume z; refine ∧ₑ₂ (int_mem (from_int z)) (∃ᵢ z (eq_refl (from_int z))) end;

opaque symbol zero_in_int : π (𝟎 ϵ INT) ≔ from_int_in_int Z0;

opaque symbol le_intro (x y : τ ι) : π (to_int x ≤ to_int y) → π (leq x y) ≔
begin assume x y h; refine =⇒ (eq_sym (le_def x y)) h end;
opaque symbol le_elim (x y : τ ι) : π (leq x y) → π (to_int x ≤ to_int y) ≔
begin assume x y h; refine =⇒ (le_def x y) h end;

// to_int distributes over plus/neg (from plus_def/neg_def + the retract).
opaque symbol to_int_add (x y : τ ι) : π (to_int (plus x y) = to_int x + to_int y) ≔
begin assume x y; rewrite (plus_def x y); reflexivity end;
opaque symbol to_int_neg (x : τ ι) : π (to_int (neg x) = — (to_int x)) ≔
begin assume x; rewrite (neg_def x); reflexivity end;
// minus = plus x (neg y); unfold directly (simplify would also unfold Z's ≤).
opaque symbol sub_def (x y : τ ι) : π (minus x y = plus x (neg y)) ≔ begin reflexivity end;
opaque symbol to_int_sub (x y : τ ι) : π (to_int (minus x y) = to_int x + (— (to_int y))) ≔
begin assume x y; rewrite (sub_def x y); rewrite (to_int_add x (neg y)); rewrite (to_int_neg y); reflexivity end;

// neg/plus land in from_int's range, so their `ϵ INT` discharges with no premise.
opaque symbol neg_in_int (a : τ ι) : π (neg a ϵ INT) ≔
begin assume a; rewrite (neg_def a); refine from_int_in_int (— (to_int a)) end;
opaque symbol add_in_int (a b : τ ι) : π (plus a b ϵ INT) ≔
begin assume a b; rewrite (plus_def a b); refine from_int_in_int (to_int a + to_int b) end;
opaque symbol mult_in_int (a b : τ ι) : π (mult a b ϵ INT) ≔
begin assume a b; rewrite (mult_def a b); refine from_int_in_int (to_int a * to_int b) end;

// Reflect a τ ι equality onto ℤ: with both sides in INT, `to_int x = to_int y` lifts
// to `x = y` (int_retract on both sides + feq).  The emitter discharges its generated
// arithmetic equalities through this — `simplify` then computes `to_int` through
// plus/neg/minus/literals, leaving a pure-ℤ goal that Stdlib.Z reductions + a small
// reorder rewrite chain close.  Replaces the inlined int_retract/feq/eq_sym scaffolding.
opaque symbol toint_eq (x y : τ ι) (hx : π (x ϵ INT)) (hy : π (y ϵ INT))
  : π (to_int x = to_int y) → π (x = y) ≔
begin assume x y hx hy h;
  rewrite (int_retract x hx); rewrite (int_retract y hy); refine feq from_int h end;

// ---- Z-level helpers (pure ℤ; the τ ι laws refine these) ----
// Kept on ℤ so rewrite matches the + subterms directly.

opaque symbol Z_sub_add (a b : ℤ) : π ((a + (— b)) + b = a) ≔
begin
  assume a b; rewrite +_assoc a (— b) b; rewrite +_com (— b) b;
  rewrite -_same b; reflexivity
end;

opaque symbol Z_neg_add (b : ℤ) : π ((— b) + b = 0) ≔
begin assume b; rewrite +_com (— b) b; refine -_same b end;

opaque symbol Z_sub_leq (a b : ℤ) : π (a ≤ b) → π ((a + (— b)) ≤ 0) ≔
begin assume a b h; rewrite left (-_same b); refine ≤_compat_add a b (— b) h end;

opaque symbol Z_leq_of_sub (a b : ℤ) : π ((a + (— b)) ≤ 0) → π (a ≤ b) ≔
begin assume a b h; rewrite left (Z_sub_add a b); refine ≤_compat_add (a + (— b)) 0 b h end;

opaque symbol Z_neg_leq (a : ℤ) : π ((— a) ≤ 0) → π (0 ≤ a) ≔
begin assume a h; rewrite left (Z_neg_add a); refine ≤_compat_add (— a) 0 a h end;

// ---- Laws — discretely ordered abelian group on τ ι ----

opaque symbol leq_refl (x : τ ι) : π (leq x x) ≔
begin assume x; refine le_intro x x (≤_refl (to_int x)) end;

opaque symbol leq_trans (x y z : τ ι) :
  π (leq x y) → π (leq y z) → π (leq x z) ≔
begin assume x y z h1 h2;
  refine le_intro x z (≤_trans (to_int x) (to_int y) (to_int z)
    (le_elim x y h1) (le_elim y z h2)) end;

// Antisymmetry recovers x = y, so it needs both in INT.
opaque symbol leq_antisym (x y : τ ι) (hx : π (x ϵ INT)) (hy : π (y ϵ INT)) :
  π (leq x y) → π (leq y x) → π (x = y) ≔
begin
  assume x y hx hy hxy hyx;
  have h : π (to_int x = to_int y)
    { refine ≤_antisym (to_int x) (to_int y) (le_elim x y hxy) (le_elim y x hyx) };
  rewrite (int_retract x hx); rewrite (int_retract y hy); refine feq from_int h
end;

opaque symbol add_comm (x y : τ ι) : π (plus x y = plus y x) ≔
begin assume x y; rewrite (plus_def x y); rewrite (plus_def y x); refine feq from_int (+_com (to_int x) (to_int y)) end;

opaque symbol add_assoc (x y z : τ ι) : π (plus (plus x y) z = plus x (plus y z)) ≔
begin assume x y z;
  rewrite (plus_def (plus x y) z); rewrite (plus_def x (plus y z));
  rewrite (to_int_add x y); rewrite (to_int_add y z);
  refine feq from_int (+_assoc (to_int x) (to_int y) (to_int z)) end;

// Right identity only on INT (recovers x); emitter supplies `ϵ INT`.
opaque symbol add_zero (x : τ ι) (hx : π (x ϵ INT)) : π (plus x 𝟎 = x) ≔
begin assume x hx; rewrite (plus_def x 𝟎); symmetry; refine int_retract x hx end;

opaque symbol one_not_leq_zero : π (¬ (leq 𝟏 𝟎)) ≔
begin assume h; refine (le_elim 𝟏 𝟎 h) ⊤ᵢ end;

// Discreteness: nothing strictly between 𝟎 and 𝟏 (compare H p is never Gt).
opaque symbol one_le_pos (p : ℙ) : π ((Zpos H) ≤ (Zpos p)) ≔
begin
  induction
  { assume q ih k; refine k }
  { assume q ih k; refine k }
  { assume k; refine k }
end;

opaque symbol Z_discrete (z : ℤ) : π (¬ (z ≤ 0)) → π (1 ≤ z) ≔
begin
  induction
  { assume h; refine ⊥ₑ (h _); assume k; refine k }
  { assume p h; refine one_le_pos p }
  { assume p h; refine ⊥ₑ (h _); assume k; refine k }
end;

opaque symbol discrete (x : τ ι) : π (¬ (leq x 𝟎)) → π (leq 𝟏 x) ≔
begin assume x h;
  refine le_intro 𝟏 x (Z_discrete (to_int x) (λ hz, h (le_intro x 𝟎 hz))) end;

// ---- Derived lemmas (congruences + variants of the axioms) ----
// Used by the emitter's generated equality proofs (arithmetic-reorder bridges).

opaque symbol add_congR (a : τ ι) [b b' : τ ι] :
  π (b = b') → π (plus a b = plus a b') ≔
begin assume a b b' h; rewrite h; reflexivity end;

opaque symbol leq_subst_l [a b : τ ι] :
  π (a = b) → π (leq b 𝟎) → π (leq a 𝟎) ≔
begin assume a b h hb; rewrite h; refine hb end;

opaque symbol zero_add (x : τ ι) (hx : π (x ϵ INT)) : π (plus 𝟎 x = x) ≔
begin assume x hx; rewrite (plus_def 𝟎 x); symmetry; refine int_retract x hx end;

opaque symbol neg_add (x : τ ι) : π (plus (neg x) x = 𝟎) ≔
begin assume x; rewrite (plus_def (neg x) x); rewrite (to_int_neg x); refine feq from_int (Z_neg_add (to_int x)) end;

// Sum of two non-positives is non-positive.
opaque symbol add_leq_zero (x y : τ ι) :
  π (leq x 𝟎) → π (leq y 𝟎) → π (leq (plus x y) 𝟎) ≔
begin
  assume x y hx hy;
  refine le_intro (plus x y) 𝟎 _; rewrite (to_int_add x y);
  refine ≤_trans (to_int x + to_int y) (to_int y) 0 _ (le_elim y 𝟎 hy);
  refine ≤_compat_add (to_int x) 0 (to_int y) (le_elim x 𝟎 hx)
end;

// leq x y ↔ leq (minus x y) 𝟎. Used by AR3, AR5–AR8, AR13.
opaque symbol sub_leq (x y : τ ι) : π (leq x y) → π (leq (minus x y) 𝟎) ≔
begin assume x y h; refine le_intro (minus x y) 𝟎 _;
  rewrite (to_int_sub x y); refine Z_sub_leq (to_int x) (to_int y) (le_elim x y h) end;

opaque symbol leq_of_sub (x y : τ ι) : π (leq (minus x y) 𝟎) → π (leq x y) ≔
begin assume x y h; refine le_intro x y (Z_leq_of_sub (to_int x) (to_int y) _);
  rewrite left (to_int_sub x y); refine le_elim (minus x y) 𝟎 h end;

// neg flips leq. Used by AR5, AR6.
opaque symbol neg_leq_zero (a : τ ι) : π (leq (neg a) 𝟎) → π (leq 𝟎 a) ≔
begin assume a h; refine le_intro 𝟎 a (Z_neg_leq (to_int a) _);
  rewrite left (to_int_neg a); refine le_elim (neg a) 𝟎 h end;

