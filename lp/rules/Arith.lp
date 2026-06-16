// Arithmetic (§A.14) — shallow encoding
// Uses ≤ and leq_refl from B.lp.
require open pp2lp.B pp2lp.Int pp2lp.Quant pp2lp.rules.Res;

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

// Bridge lemma: `𝟏 - (— x) = 𝟏 + x` (Z.—_idem on the projection; unconditional).
opaque symbol ar3_bridge_neg (x : τ ι) : π (𝟏 - (— x) = 𝟏 + x) ≔
begin
  assume x;
  have e : π (Stdlib.Z.+ (to_int 𝟏) (Stdlib.Z.— (Stdlib.Z.— (to_int x)))
             = Stdlib.Z.+ (to_int 𝟏) (to_int x))
    { rewrite Stdlib.Z.—_idem (to_int x); reflexivity };
  refine feq from_int e
end;

// ---- AR3_F: PP's forward normalisation `¬(a ≤ 𝟎) ⟿ r ≤ 𝟎` (r = 𝟏−a) ----
//
// PP's solver rewrites `¬(a ≤ 𝟎)` to `r ≤ 𝟎` in place (the AR3_F replay
// step), where `r` is its arithmetic-normalised form of `𝟏 − a`.  LP keeps
// the literal `¬(a ≤ 𝟎)`, so the two views diverge at the consuming leaf.
// These bridge the gap *ground* (after the binder is introduced — an
// under-binder rewrite crashes Lambdapi's inference): `not_leq_of_sub1`
// transports a hypothesis `𝟏 − a ≤ 𝟎` back to `¬(a ≤ 𝟎)` for an INS
// witness; `ar3f_eq` is the propositional equality the goal-side consumer
// (AXM7) transports along.  Both `1 − a ⟺ a > 𝟎 ⟺ ¬(a ≤ 𝟎)`, no `trust`.
opaque symbol not_leq_of_sub1 (a : τ ι) : π (𝟏 - a ≤ 𝟎) → π (¬ (a ≤ 𝟎)) ≔
begin
  assume a h ha;
  refine one_not_leq_zero (leq_trans 𝟏 a 𝟎 (leq_of_sub 𝟏 a h) ha)
end;

opaque symbol ar3f_eq (a r : τ ι) : π (𝟏 - a = r) → π ((¬ (a ≤ 𝟎)) = (r ≤ 𝟎)) ≔
begin
  assume a r eq;
  rewrite left eq;
  refine propExt _ _ _ _
  { assume hna; refine sub_leq 𝟏 a (discrete a hna) }
  { assume hsub; refine not_leq_of_sub1 a hsub }
end;

// (a ≤ b) = (a − b ≤ 𝟎), as a propositional equality (AR2's `a > b`, the
// emitter transports `prove_gt_zero (a−b)` back along its negation).
opaque symbol sub_leq_eq (a b : τ ι) : π ((a ≤ b) = (a - b ≤ 𝟎)) ≔
begin assume a b; refine propExt _ _ (sub_leq a b) (leq_of_sub a b) end;

// AR3_F is *not* a single symbol: PP's forward normalisation rewrites a
// `¬(a ≤ 𝟎)` occurrence in place, at an arbitrary binder-nested position.
// The emitter (translate.ml `ar3f_cong`) builds the congruence proof for
// that exact position by composing `imp_cong_l/r`, `not_cong`,
// `conj_snoc_last_cong`, and `!!_cong` (recursing under the binder) down to
// an `ar3f_eq` leaf, then transports the goal with `=⇒`.

// AR4: F ≤ 0 in H; E + F > 0 (solver-confirmed) → H ⊢ E ≤ 0 ⇒ R
// If E ≤ 0 and F ≤ 0 then E + F ≤ 0, contradicting E + F > 0.
// E, F implicit: E inferred from the `(E ≤ 𝟎)` goal, F from the `F ≤ 𝟎` premise —
// both via the Int.lp `to_int`/`isGt` unification rules (a defined `≤` would
// otherwise hide them behind `to_int (from_int …)`).
opaque symbol AR4 [E : τ ι] [R : Prop] [F : τ ι]
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
opaque symbol AR5 [a : τ ι] [R : Prop] (hai : π (a ϵ INT))
  : π (a ≪ 𝟎)
  → π ((— a ≤ 𝟎) ⇒ ((a = 𝟎) ⇒ R))
  → π ((— a ≤ 𝟎) ⇒ R) ≔
begin
  assume a R hai ha hR hna;
  refine hR hna (leq_antisym a 𝟎 hai zero_in_int ha (neg_leq_zero a hna))
end;

// AR6: —a ≤ 0 in H, a ≤ 0 antecedent ⇒ a = 0 (dual to AR5).
opaque symbol AR6 [a : τ ι] [R : Prop] (hai : π (a ϵ INT))
  : π ((— a) ≤ 𝟎)
  → π ((a ≤ 𝟎) ⇒ ((a = 𝟎) ⇒ R))
  → π ((a ≤ 𝟎) ⇒ R) ≔
begin
  assume a R hai hna hR ha;
  refine hR ha (leq_antisym a 𝟎 hai zero_in_int ha (neg_leq_zero a hna))
end;

// AR7: c+b ≤ 0 in H, a+c = 0, a−b ≤ 0 antecedent ⇒ a = b.
// From a+c = 0: c = —a. So c+b ≤ 0 becomes —a+b = b−a ≤ 0, i.e. b ≤ a.
// Combined with a−b ≤ 0 (i.e. a ≤ b), antisymmetry gives a = b.
// hR's equality is stated `b = a` (not `a = b`): PP records the antisymmetry
// equality bare-variable-first (e.g. `b = -1+a`), and the emitter feeds that
// child directly into the `hR` slot, so the lemma must match that orientation.
opaque symbol AR7 [a b : τ ι] (c : τ ι) [R : Prop]
  (hai : π (a ϵ INT)) (hbi : π (b ϵ INT)) (hci : π (c ϵ INT))
  : π ((c + b) ≪ 𝟎)
  → π ((a + c) = 𝟎)
  → π ((b = a) ⇒ (((a - b) ≤ 𝟎) ⇒ R))
  → π (((a - b) ≤ 𝟎) ⇒ R) ≔
begin
  assume a b c R hai hbi hci hcb hac hR hab;
  have heq_c : π (c = — a) {
    rewrite left (zero_add c hci);
    rewrite left neg_add a;
    rewrite add_assoc (— a) a c;
    rewrite hac;
    refine add_zero (— a) (neg_in_int a)
  };
  have ba_leq : π (b - a ≤ 𝟎) {
    refine leq_subst_l (eq_trans (add_congR b (eq_sym heq_c)) (add_comm b c)) hcb
  };
  refine hR (eq_sym (leq_antisym a b hai hbi (leq_of_sub a b hab) (leq_of_sub b a ba_leq))) hab
end;

// AR8: dual to AR7 — a−b ≤ 0 in H, a+c = 0, c+b ≤ 0 antecedent ⇒ a = b.
// `b = a` orientation, as for AR7 above.
opaque symbol AR8 (a : τ ι) [b c : τ ι] [R : Prop]
  (hai : π (a ϵ INT)) (hbi : π (b ϵ INT)) (hci : π (c ϵ INT))
  : π ((a - b) ≪ 𝟎)
  → π ((a + c) = 𝟎)
  → π ((b = a) ⇒ (((c + b) ≤ 𝟎) ⇒ R))
  → π (((c + b) ≤ 𝟎) ⇒ R) ≔
begin
  assume a b c R hai hbi hci hab hac hR hcb;
  have heq_c : π (c = — a) {
    rewrite left (zero_add c hci);
    rewrite left neg_add a;
    rewrite add_assoc (— a) a c;
    rewrite hac;
    refine add_zero (— a) (neg_in_int a)
  };
  have ba_leq : π (b - a ≤ 𝟎) {
    refine leq_subst_l (eq_trans (add_congR b (eq_sym heq_c)) (add_comm b c)) hcb
  };
  refine hR (eq_sym (leq_antisym a b hai hbi (leq_of_sub a b hab) (leq_of_sub b a ba_leq))) hcb
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
// a, b explicit: a defined `≤` can't infer them from `(a ≤ b)` (emitter supplies).
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
// equality. Other AR_1 forms are proven outright or bridge the equality with
// a generated proof (AR3'_1); shapes the chain emit can't thread fail loud —
// none emit `trust`.

// (E ≤ E) ⇒ R ≡ R — the antecedent is always true (leq_refl).  Mirrors evr3_eq.
opaque symbol ar1_eq [E : τ ι] [R : Prop] : π (((E ≤ E) ⇒ R) = R) ≔
begin
  assume E R;
  refine propExt _ _ _ _
    { assume h; refine h (leq_refl E) }
    { assume h h0; refine h }
end;

symbol AR1_1 [E : τ ι] [R : Prop]
  (r : Res R) : Res ((E ≤ E) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (@ar1_eq E R) (res_eq r));

symbol AR2_1 [a b : τ ι] [R : Prop] (h : π (a > b))
  : Res ((a ≤ b) ⇒ R) ≔ mk_0 (prop_eq_top (@AR2 a b R h));

symbol AR3_1 (a : τ ι) [R : Prop]
  (r : Res ((𝟏 - a ≤ 𝟎) ⇒ R)) : Res (¬ (a ≤ 𝟎) ⇒ R)
  ≔ mk_1 (res_tm r)
       (eq_trans (imp_cong_l (ar3f_eq a (𝟏 - a) (eq_refl (𝟏 - a)))) (res_eq r));

// AR3'_1: bridged Res-chain AR3, for when PP's solver records the sub-premise
// `𝟏 - a` in a different (neg-normalised) term order `r`.  Both steps are now
// real: `¬(a≤𝟎) = (r≤𝟎)` is `ar3f_eq a r eq` and `eq : 𝟏-a=r` is the
// emitter-supplied equality (cf. AR3_1, which is the special case r = 𝟏-a).
symbol AR3'_1 (a r : τ ι) [R : Prop]
  (eq : π (𝟏 - a = r))
  (cont : Res ((r ≤ 𝟎) ⇒ R)) : Res (¬ (a ≤ 𝟎) ⇒ R)
  ≔ mk_1 (res_tm cont)
       (eq_trans (imp_cong_l (ar3f_eq a r eq)) (res_eq cont));

// AR4_1: reuse the base rule (F≤𝟎, (E+F)>𝟎 solver facts as evidence).
symbol AR4_1 [E : τ ι] [R : Prop] (F : τ ι)
  (hf : π (F ≤ 𝟎)) (hef : π ((E + F) > 𝟎)) : Res ((E ≤ 𝟎) ⇒ R)
  ≔ mk_0 (prop_eq_top (@AR4 E R F hf hef));

// AR5/AR6: antisymmetry-to-zero — `a = 𝟎` (from the two bounds) lets the inner
// `(a=𝟎) ⇒` be stripped (imp_known_drop under imp_cong_r).
symbol AR5_1 [a : τ ι] [R : Prop] (h0 : π (a = 𝟎))
  (r : Res ((— a ≤ 𝟎) ⇒ ((a = 𝟎) ⇒ R))) : Res ((— a ≤ 𝟎) ⇒ R)
  ≔ mk_1 (res_tm r)
       (eq_trans (eq_sym (imp_cong_r (imp_known_drop h0))) (res_eq r));

symbol AR6_1 [a : τ ι] [R : Prop] (h0 : π (a = 𝟎))
  (r : Res ((a ≤ 𝟎) ⇒ ((a = 𝟎) ⇒ R))) : Res ((a ≤ 𝟎) ⇒ R)
  ≔ mk_1 (res_tm r)
       (eq_trans (eq_sym (imp_cong_r (imp_known_drop h0))) (res_eq r));

// AR7/AR8: the antisymmetry `a = b` strips the leading `(a=b) ⇒`.
symbol AR7_1 [a b : τ ι] (c : τ ι) [R : Prop] (hab : π (a = b))
  (r : Res ((a = b) ⇒ (((a - b) ≤ 𝟎) ⇒ R)))
  : Res (((a - b) ≤ 𝟎) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (eq_sym (imp_known_drop hab)) (res_eq r));

symbol AR8_1 (a : τ ι) [b c : τ ι] [R : Prop] (hab : π (a = b))
  (r : Res ((a = b) ⇒ (((c + b) ≤ 𝟎) ⇒ R)))
  : Res (((c + b) ≤ 𝟎) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (eq_sym (imp_known_drop hab)) (res_eq r));

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
  ≔ mk_1 (res_tm r) (eq_trans (imp_cong_l heq) (res_eq r));

symbol AR11_1 [E : τ ι] [P : Prop] : Res (¬ (E ≤ E) ⇒ P)
  ≔ mk_0 (prop_eq_top (@AR11 E P));  // ¬(E≤E) absurd (leq_refl) ⇒ vacuously ⊤

symbol AR12_1 [a b : τ ι] [P : Prop] (h : π (a ≤ b))
  (r : Res P) : Res ((a ≤ b) ⇒ P)
  ≔ mk_1 (res_tm r) (eq_trans (imp_known_drop h) (res_eq r));

// AR13: `¬(a ≤ 𝟎)` is the result; supply it as evidence (a > 𝟎 from the solver).
symbol AR13_1 [a b : τ ι] (h : π (¬ (a ≤ 𝟎))) : Res (¬ (a ≤ 𝟎))
  ≔ mk_0 (prop_eq_top h);
