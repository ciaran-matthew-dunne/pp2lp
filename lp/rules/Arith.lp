// Arithmetic (§A.14) — shallow encoding
// Uses ≤ and leq_refl from B.lp.
require open pp2lp.B pp2lp.Quant pp2lp.rules.Res;

// ---- AR1-3: Reflexivity of ≤ ----

opaque symbol AR1 [E : τ ι] [R : Prop]
  : π R
  → π ((E ≤ E) ⇒ R) ≔
begin
  assume E R h h0; refine h
end;

opaque symbol AR2 [a b : τ ι] [R : Prop]
  : π (a > b)
  → π ((a ≤ b) ⇒ R) ≔
begin
  assume a b R hgt h;
  refine ⊥ₑ (hgt h)
end;

opaque symbol AR3 (a : τ ι) [R : Prop]
  : π ((𝟏 - a ≤ 𝟎) ⇒ R)
  → π (¬ (a ≤ 𝟎) ⇒ R) ≔
begin
  assume a R h hna;
  refine h (sub_leq 𝟏 a (discrete a hna))
end;

// AR3' — bridged variant for the case where PP's solver normalises the
// AR3 sub-premise `(𝟏 - a) ≤ 𝟎` to `r ≤ 𝟎` for some r ≠ (𝟏 - a). The
// emitter passes (a, r, eq) where eq : (𝟏 - a) = r, and the inner proof
// works directly with (r ≤ 𝟎) ⇒ R.
opaque symbol AR3' (a r : τ ι) [R : Prop]
  : π (𝟏 - a = r)
  → π ((r ≤ 𝟎) ⇒ R)
  → π (¬ (a ≤ 𝟎) ⇒ R) ≔
begin
  assume a r R eq h;
  refine AR3 a _;
  assume h0;
  refine h _;
  rewrite left eq;
  refine h0
end;

// Bridge lemma: `𝟏 - (— x)` reduces to `𝟏 + x` after `neg_neg`.
opaque symbol ar3_bridge_neg (x : τ ι) : π (𝟏 - (— x) = 𝟏 + x) ≔
begin
  assume x; simplify; rewrite neg_neg x; reflexivity
end;

// AR4: F ≤ 0 in H; E + F > 0 (solver-confirmed) → H ⊢ E ≤ 0 ⇒ R
// If E ≤ 0 and F ≤ 0 then E + F ≤ 0, contradicting E + F > 0.
opaque symbol AR4 [E : τ ι] [R : Prop] (F : τ ι)
  : π (F ≤ 𝟎)
  → π ((E + F) > 𝟎)
  → π ((E ≤ 𝟎) ⇒ R) ≔
begin
  assume E R F hF hEF hE;
  refine ⊥ₑ (hEF (add_leq_zero E F hE hF))
end;

// AR5: a ≤ 0 in H, —a ≤ 0 antecedent ⇒ a = 0 (antisymmetry of ≤).
//
// The B-book premise is `(a = 𝟎) ⇒ ((—a ≤ 𝟎) ⇒ R)`, but PP commutes
// the antecedents (presumably via classical equivalence inside its
// solver) before chaining into AR12. We use the commuted form here so
// the LP rule matches PP's emission shape directly.
opaque symbol AR5 [a : τ ι] [R : Prop]
  : π (a ≪ 𝟎)
  → π ((— a ≤ 𝟎) ⇒ ((a = 𝟎) ⇒ R))
  → π ((— a ≤ 𝟎) ⇒ R) ≔
begin
  assume a R ha hR hna;
  refine hR hna (leq_antisym a 𝟎 ha (neg_leq_zero a hna))
end;

// AR6: —a ≤ 0 in H, a ≤ 0 antecedent ⇒ a = 0 (dual to AR5).
opaque symbol AR6 [a : τ ι] [R : Prop]
  : π ((— a) ≤ 𝟎)
  → π ((a ≤ 𝟎) ⇒ ((a = 𝟎) ⇒ R))
  → π ((a ≤ 𝟎) ⇒ R) ≔
begin
  assume a R hna hR ha;
  refine hR ha (leq_antisym a 𝟎 ha (neg_leq_zero a hna))
end;

// AR7: c+b ≤ 0 in H, a+c = 0, a−b ≤ 0 antecedent ⇒ a = b.
// From a+c = 0: c = —a. So c+b ≤ 0 becomes —a+b = b−a ≤ 0, i.e. b ≤ a.
// Combined with a−b ≤ 0 (i.e. a ≤ b), antisymmetry gives a = b.
opaque symbol AR7 [a b : τ ι] (c : τ ι) [R : Prop]
  : π ((c + b) ≪ 𝟎)
  → π ((a + c) = 𝟎)
  → π ((a = b) ⇒ (((a - b) ≤ 𝟎) ⇒ R))
  → π (((a - b) ≤ 𝟎) ⇒ R) ≔
begin
  assume a b c R hcb hac hR hab;
  have heq_c : π (c = — a) {
    rewrite left zero_add c;
    rewrite left neg_add a;
    rewrite add_assoc (— a) a c;
    rewrite hac;
    refine add_zero (— a)
  };
  have ba_leq : π (b - a ≤ 𝟎) {
    simplify;
    rewrite left heq_c;
    rewrite add_comm b c;
    refine hcb
  };
  refine hR (leq_antisym a b (leq_of_sub a b hab) (leq_of_sub b a ba_leq)) hab
end;

// AR8: dual to AR7 — a−b ≤ 0 in H, a+c = 0, c+b ≤ 0 antecedent ⇒ a = b.
opaque symbol AR8 (a : τ ι) [b c : τ ι] [R : Prop]
  : π ((a - b) ≪ 𝟎)
  → π ((a + c) = 𝟎)
  → π ((a = b) ⇒ (((c + b) ≤ 𝟎) ⇒ R))
  → π (((c + b) ≤ 𝟎) ⇒ R) ≔
begin
  assume a b c R hab hac hR hcb;
  have heq_c : π (c = — a) {
    rewrite left zero_add c;
    rewrite left neg_add a;
    rewrite add_assoc (— a) a c;
    rewrite hac;
    refine add_zero (— a)
  };
  have ba_leq : π (b - a ≤ 𝟎) {
    simplify;
    rewrite left heq_c;
    rewrite add_comm b c;
    refine hcb
  };
  refine hR (leq_antisym a b (leq_of_sub a b hab) (leq_of_sub b a ba_leq)) hcb
end;

opaque symbol AR9 [E : τ ι] (F : τ ι) [R : Prop]
  : π (E = F)
  → π ((F ≤ 𝟎) ⇒ R)
  → π ((E ≤ 𝟎) ⇒ R) ≔
begin
  assume E F R heq hf h;
  have h2 : π (F ≤ 𝟎) { rewrite left heq; refine h };
  refine hf h2
end;


// AR10: solver(P) = Q; H ⊢ Q ⇒ R → H ⊢ P ⇒ R
opaque symbol AR10 [P Q R : Prop]
  : π (P = Q)
  → π (Q ⇒ R)
  → π (P ⇒ R) ≔
begin
  assume P Q R heq h1 h2;
  refine h1 (=⇒ heq h2)
end;

// AR11: H ⊢ ¬(x ≤ x) ⇒ P
opaque symbol AR11 [E : τ ι] [P : Prop]
  : π (¬ (E ≤ E) ⇒ P) ≔
begin
  assume E P h; refine ⊥ₑ (h (leq_refl E))
end;

// AR12: H, (a ≤ b) ⊢ P → H ⊢ (a ≪ b) ⇒ P in the B-book; PP never emits ≪
// on the wire, so we type the antecedent with ≤ directly. (B.lp also aliases
// ≪ ≔ ≤ for AR5–AR8, AR13 whose signatures still mention ≪.)
opaque symbol AR12 [a b : τ ι] [P : Prop]
  : (π (a ≤ b) → π P)
  → π ((a ≤ b) ⇒ P) ≔
begin
  assume a b P h1 h2; refine h1 h2
end;

// AR13: solver(1−a) = b; b ≤ 0 → ¬(a ≪ 0)
// Substitute b → 1−a, then 1−a ≤ 0 ⇒ 1 ≤ a; combined with a ≤ 0
// (the assumed antecedent of ¬), 1 ≤ 0 — contradicting one_not_leq_zero.
opaque symbol AR13 [a b : τ ι]
  : π ((𝟏 - a) = b)
  → π (b ≤ 𝟎)
  → π (¬ (a ≤ 𝟎)) ≔
begin
  assume a b heq hb ha;
  have h1 : π (𝟏 - a ≤ 𝟎) { rewrite heq; refine hb };
  refine one_not_leq_zero (leq_trans 𝟏 a 𝟎 (leq_of_sub 𝟏 a h1) ha)
end;

// ---- `_1` (Result-form) variants — §8.13 ----
//
// AR9_1 below uses leq_zero_eq to bridge the solver-supplied
// equality. Other AR rules use `trust` for the propositional equality
// since the chain emit doesn't thread the solver side-conditions.

symbol AR1_1 [E : τ ι] [R : Prop]
  (r : Res R) : Res ((E ≤ E) ⇒ R)
  ≔ mk_1 (res_tm r) trust;

symbol AR2_1 [a b : τ ι] [R : Prop] : Res ((a ≤ b) ⇒ R) ≔ mk_1 ⊤ trust;

symbol AR3_1 (a : τ ι) [R : Prop]
  (r : Res ((𝟏 - a ≤ 𝟎) ⇒ R)) : Res (¬ (a ≤ 𝟎) ⇒ R)
  ≔ mk_1 (res_tm r) trust;

// AR3'_1: bridged Res-chain AR3, for when PP's solver records the sub-premise
// `𝟏 - a` in a different (neg-normalised) term order `r`.  The `¬(a≤𝟎) =
// (𝟏-a≤𝟎)` step is the AR3 logical bridge (trusted, as in AR3_1); the
// `(𝟏-a≤𝟎) = (r≤𝟎)` step is the real, emitter-supplied equality `eq : 𝟏-a=r`.
symbol AR3'_1 (a r : τ ι) [R : Prop]
  (eq : π (𝟏 - a = r))
  (cont : Res ((r ≤ 𝟎) ⇒ R)) : Res (¬ (a ≤ 𝟎) ⇒ R)
  ≔ mk_1 (res_tm cont)
       (eq_trans trust
          (eq_trans (imp_cong_l (leq_zero_eq eq)) (res_eq cont)));

symbol AR4_1 [E : τ ι] [R : Prop] (F : τ ι) : Res ((E ≤ 𝟎) ⇒ R)
  ≔ mk_1 ⊤ trust;

symbol AR5_1 [a : τ ι] [R : Prop]
  (r : Res ((— a ≤ 𝟎) ⇒ ((a = 𝟎) ⇒ R))) : Res ((— a ≤ 𝟎) ⇒ R)
  ≔ mk_1 (res_tm r) trust;

symbol AR6_1 [a : τ ι] [R : Prop]
  (r : Res ((a ≤ 𝟎) ⇒ ((a = 𝟎) ⇒ R))) : Res ((a ≤ 𝟎) ⇒ R)
  ≔ mk_1 (res_tm r) trust;

symbol AR7_1 [a b : τ ι] (c : τ ι) [R : Prop]
  (r : Res ((a = b) ⇒ (((a - b) ≤ 𝟎) ⇒ R)))
  : Res (((a - b) ≤ 𝟎) ⇒ R)
  ≔ mk_1 (res_tm r) trust;

symbol AR8_1 (a : τ ι) [b c : τ ι] [R : Prop]
  (r : Res ((a = b) ⇒ (((c + b) ≤ 𝟎) ⇒ R)))
  : Res (((c + b) ≤ 𝟎) ⇒ R)
  ≔ mk_1 (res_tm r) trust;

// AR9_1: solver-confirmed equality on the antecedent of a Res chain.
// Mirrors the spec AR9 but in Res form: given a bridge proof E = F, a
// chain proving (F ≤ 0 ⇒ R) lifts to one for (E ≤ 0 ⇒ R). F is
// explicit so emit sites can pin it via the PP-supplied solver result.
// Transparent — `res_tm (AR9_1 F he r)` reduces to `res_tm r` so the
// outer chain can decompose the resulting Prop.
symbol AR9_1 [E : τ ι] (F : τ ι) [R : Prop]
  (he : π (E = F))
  (r : Res ((F ≤ 𝟎) ⇒ R)) : Res ((E ≤ 𝟎) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (imp_cong_l (leq_zero_eq he)) (res_eq r));

symbol AR10_1 [P Q R : Prop]
  (heq : π (P = Q)) (r : Res (Q ⇒ R)) : Res (P ⇒ R)
  ≔ mk_1 (res_tm r) trust;

symbol AR11_1 [E : τ ι] [P : Prop] : Res (¬ (E ≤ E) ⇒ P) ≔ mk_1 ⊤ trust;

symbol AR12_1 [a b : τ ι] [P : Prop]
  (r : Res P) : Res ((a ≤ b) ⇒ P)
  ≔ mk_1 (res_tm r) trust;

symbol AR13_1 [a b : τ ι] : Res (¬ (a ≤ 𝟎)) ≔ mk_1 ⊤ trust;
