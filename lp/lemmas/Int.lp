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

// to_int distributes over plus/neg (from add_def/neg_def + the retract).
opaque symbol to_int_add (x y : τ ι) : π (to_int (plus x y) = to_int x + to_int y) ≔
begin assume x y; rewrite (add_def x y); reflexivity end;
opaque symbol to_int_neg (x : τ ι) : π (to_int (neg x) = — (to_int x)) ≔
begin assume x; rewrite (neg_def x); reflexivity end;
// minus = plus x (neg y); unfold directly (simplify would also unfold Z's ≤).
opaque symbol sub_def (x y : τ ι) : π (minus x y = plus x (neg y)) ≔ begin reflexivity end;
opaque symbol to_int_sub (x y : τ ι) : π (to_int (minus x y) = to_int x + (— (to_int y))) ≔
begin assume x y; rewrite (sub_def x y); rewrite (to_int_add x (neg y)); rewrite (to_int_neg y); reflexivity end;

// Fold two ℤ literals into one (Z computes the sum); lit_neg first flips a negated
// literal. Lets the emitter collapse a run of literal atoms (𝟐 + 𝟑 ↦ 𝟓).
opaque symbol lit_add (a b : ℤ) : π (plus (from_int a) (from_int b) = from_int (a + b)) ≔
begin assume a b; rewrite (add_def (from_int a) (from_int b)); reflexivity end;
opaque symbol lit_neg (z : ℤ) : π (neg (from_int z) = from_int (— z)) ≔
begin assume z; rewrite (neg_def (from_int z)); reflexivity end;

// neg/plus land in from_int's range, so their `ϵ INT` discharges with no premise.
opaque symbol neg_in_int (a : τ ι) : π (neg a ϵ INT) ≔
begin assume a; rewrite (neg_def a); refine from_int_in_int (— (to_int a)) end;
opaque symbol add_in_int (a b : τ ι) : π (plus a b ϵ INT) ≔
begin assume a b; rewrite (add_def a b); refine from_int_in_int (to_int a + to_int b) end;

// ---- Z-level helpers (pure ℤ; the τ ι laws refine these) ----
// Kept on ℤ so rewrite matches the + subterms directly.

opaque symbol Z_add_leq_l (a b c : ℤ) : π (a ≤ b) → π ((c + a) ≤ (c + b)) ≔
begin
  assume a b c h; rewrite +_com c a; rewrite +_com c b;
  refine ≤_compat_add a b c h
end;

opaque symbol Z_leq_succ (a : ℤ) : π (a ≤ (a + 1)) ≔
begin
  assume a; have h01 : π (0 ≤ 1) { assume k; refine k };
  rewrite +_com a 1; refine ≤_compat_add 0 1 a h01
end;

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
begin assume x y; rewrite (add_def x y); rewrite (add_def y x); refine feq from_int (+_com (to_int x) (to_int y)) end;

opaque symbol add_assoc (x y z : τ ι) : π (plus (plus x y) z = plus x (plus y z)) ≔
begin assume x y z;
  rewrite (add_def (plus x y) z); rewrite (add_def x (plus y z));
  rewrite (to_int_add x y); rewrite (to_int_add y z);
  refine feq from_int (+_assoc (to_int x) (to_int y) (to_int z)) end;

// Right identity only on INT (recovers x); emitter supplies `ϵ INT`.
opaque symbol add_zero (x : τ ι) (hx : π (x ϵ INT)) : π (plus x 𝟎 = x) ≔
begin assume x hx; rewrite (add_def x 𝟎); symmetry; refine int_retract x hx end;

opaque symbol add_neg (x : τ ι) : π (plus x (neg x) = 𝟎) ≔
begin assume x; rewrite (add_def x (neg x)); rewrite (to_int_neg x); refine feq from_int (-_same (to_int x)) end;

// Translation invariance.
opaque symbol add_leq_l (x y z : τ ι) : π (leq x y) → π (leq (plus z x) (plus z y)) ≔
begin assume x y z h; refine le_intro (plus z x) (plus z y) _;
  rewrite (to_int_add z x); rewrite (to_int_add z y);
  refine Z_add_leq_l (to_int x) (to_int y) (to_int z) (le_elim x y h) end;

opaque symbol one_not_leq_zero : π (¬ (leq 𝟏 𝟎)) ≔
begin assume h; refine (le_elim 𝟏 𝟎 h) ⊤ᵢ end;

opaque symbol zero_leq_one : π (leq 𝟎 𝟏) ≔
begin refine le_intro 𝟎 𝟏 _; assume h; refine h end;

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

opaque symbol add_congL (b : τ ι) [a a' : τ ι] :
  π (a = a') → π (plus a b = plus a' b) ≔
begin assume b a a' h; rewrite h; reflexivity end;

opaque symbol add_congR (a : τ ι) [b b' : τ ι] :
  π (b = b') → π (plus a b = plus a b') ≔
begin assume a b b' h; rewrite h; reflexivity end;

opaque symbol add_cong [a a' b b' : τ ι] :
  π (a = a') → π (b = b') → π (plus a b = plus a' b') ≔
begin assume a a' b b' ha hb; rewrite ha; rewrite hb; reflexivity end;

opaque symbol leq_subst_l [a b : τ ι] :
  π (a = b) → π (leq b 𝟎) → π (leq a 𝟎) ≔
begin assume a b h hb; rewrite h; refine hb end;

opaque symbol zero_add (x : τ ι) (hx : π (x ϵ INT)) : π (plus 𝟎 x = x) ≔
begin assume x hx; rewrite (add_def 𝟎 x); symmetry; refine int_retract x hx end;

opaque symbol neg_add (x : τ ι) : π (plus (neg x) x = 𝟎) ≔
begin assume x; rewrite (add_def (neg x) x); rewrite (to_int_neg x); refine feq from_int (Z_neg_add (to_int x)) end;

opaque symbol add_leq_r (x y z : τ ι) :
  π (leq x y) → π (leq (plus x z) (plus y z)) ≔
begin assume x y z h; refine le_intro (plus x z) (plus y z) _;
  rewrite (to_int_add x z); rewrite (to_int_add y z);
  refine ≤_compat_add (to_int x) (to_int y) (to_int z) (le_elim x y h) end;

// x ≤ x + 𝟏 — the ARITH closer chains this to refute a positive-literal sum.
opaque symbol leq_plus_one (x : τ ι) : π (leq x (plus x 𝟏)) ≔
begin assume x; refine le_intro x (plus x 𝟏) _; rewrite (to_int_add x 𝟏); refine Z_leq_succ (to_int x) end;

// Sum of two non-positives is non-positive.
opaque symbol add_leq_zero (x y : τ ι) :
  π (leq x 𝟎) → π (leq y 𝟎) → π (leq (plus x y) 𝟎) ≔
begin
  assume x y hx hy;
  refine le_intro (plus x y) 𝟎 _; rewrite (to_int_add x y);
  refine ≤_trans (to_int x + to_int y) (to_int y) 0 _ (le_elim y 𝟎 hy);
  refine ≤_compat_add (to_int x) 0 (to_int y) (le_elim x 𝟎 hx)
end;

// 𝟏 + (≥𝟎) > 𝟎 — O(1) positivity for the AR2/AR4 closer (no unary blowup).
opaque symbol pos_add (x : τ ι) : π (leq 𝟎 x) → π (¬ (leq (plus 𝟏 x) 𝟎)) ≔
begin
  assume x h hk;
  have h1 : π (1 ≤ (1 + to_int x))
    { rewrite +_com 1 (to_int x); refine ≤_compat_add 0 (to_int x) 1 (le_elim 𝟎 x h) };
  have hk2 : π ((to_int 𝟏 + to_int x) ≤ 0)
    { rewrite left (to_int_add 𝟏 x); refine le_elim (plus 𝟏 x) 𝟎 hk };
  refine (≤_trans 1 (to_int 𝟏 + to_int x) 0 h1 hk2) ⊤ᵢ
end;

// from_int (Zpos p) > 𝟎 for any magnitude p (Zpos p ≐ Z0 ↪ Gt by head match).
opaque symbol lit_pos (p : ℙ) : π (¬ (leq (from_int (Zpos p)) 𝟎)) ≔
begin assume p h; refine (le_elim (from_int (Zpos p)) 𝟎 h) ⊤ᵢ end;

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

// ---- Algebraic identities ----

opaque symbol neg_zero : π (neg 𝟎 = 𝟎) ≔
begin rewrite (neg_def 𝟎); reflexivity end;

// Involutive (recovers x, so guarded by `ϵ INT`).
opaque symbol neg_neg (x : τ ι) (hx : π (x ϵ INT)) : π (neg (neg x) = x) ≔
begin assume x hx; rewrite (neg_def (neg x)); rewrite (to_int_neg x);
  rewrite (—_idem (to_int x)); symmetry; refine int_retract x hx end;

// neg distributes over plus.
opaque symbol opp_add (x y : τ ι) : π (neg (plus x y) = plus (neg x) (neg y)) ≔
begin assume x y; rewrite (neg_def (plus x y)); rewrite (add_def (neg x) (neg y));
  rewrite (to_int_add x y); rewrite (to_int_neg x); rewrite (to_int_neg y);
  refine feq from_int (distr_—_+ (to_int x) (to_int y)) end;
