// Res.lp — Σ-type encoding of normalisation chains, self-contained.
//
// `Res t = (t' : τ a) × π (t = t')` packages a normalised term with a
// proof of equality to the original.  Each `_1` rule consumes child
// Res values and produces a new Res; chains are term-level function
// compositions (e.g. `AND2_1 (VR3_1 STOP_1)`) where `res_tm`
// projects the final normal form and `res_eq` projects the cumulative
// equality witness.  No external `_1` lemmas; every proof is inline.
//
// Helper structure:
//   - generic equality combinators (eq_trans, conj_eq, ∧_assoc, …)
//   - per-connective equality lemmas (and1_eq, and2_eq, …) — these are
//     just propositional facts about the connective transformations
//     specified by §A of the PP rule reference
//   - the `_1` rules themselves
//   - the `left_∧` autoflatten combinator (used by AND4_1 so chained
//     AND4s reduce to a left-associated conjunction without explicit
//     ∧_assoc rewrites at the call site)
//   - `ALL7_close` / `XST8_close` chain-exit operators that re-package
//     a per-tuple Res chain into the propositional form expected by
//     All.lp / Xst.lp. Quantifier-related symbols are arity-uniform
//     over `Tuple n`.

require open pp2lp.B pp2lp.Quant pp2lp.rules.All pp2lp.rules.Xst;

// (Res infrastructure — Res, mk_1, res_tm, res_eq — has moved to
//  Quant.lp so it's available to All.lp/Xst.lp where the result-based
//  ALL7 / XST8 are now defined.)

// ============================================================
// Generic equality combinators
// ============================================================

opaque symbol eq_trans [a] [P Q R : τ a]
  : π (P = Q) → π (Q = R) → π (P = R) ≔
begin assume a P Q R h1 h2; rewrite h1; refine h2 end;

// Conj congruence: lift independent equalities to their conjunction.
opaque symbol conj_eq [A B S1 S2 : Prop]
  : π (A = S1) → π (B = S2) → π ((A ∧ B) = (S1 ∧ S2)) ≔
begin
  assume A B S1 S2 h1 h2;
  rewrite h1; rewrite h2; reflexivity
end;

// Conj associativity (right ↔ left), used by ALL7/XST8 continuations
// when the inner _1 chain produced a right-assoc conjunction.
opaque symbol ∧_assoc [A B C : Prop]
  : π ((A ∧ (B ∧ C)) = ((A ∧ B) ∧ C)) ≔
begin
  assume A B C;
  refine propExt _ _ _ _
  { assume h; refine ∧ᵢ (∧ᵢ (∧ₑ₁ h) (∧ₑ₁ (∧ₑ₂ h))) (∧ₑ₂ (∧ₑ₂ h)) }
  { assume h; refine ∧ᵢ (∧ₑ₁ (∧ₑ₁ h)) (∧ᵢ (∧ₑ₂ (∧ₑ₁ h)) (∧ₑ₂ h)) }
end;

// Antecedent equivalence → implication equality (for AND5_1).
opaque symbol ante_cong [C C' R : Prop]
  : (π C → π C') → (π C' → π C) → π ((C ⇒ R) = (C' ⇒ R)) ≔
begin
  assume C C' R fwd bwd;
  refine propExt _ _ _ _
    { assume h hc'; refine h (bwd hc') }
    { assume h hc; refine h (fwd hc) }
end;

// (`!!_cong` — pointwise equality lifts to `!!` equality —
//  is provided by Quant.lp.)

// Implication right congruence.
opaque symbol imp_cong_r [P Q R : Prop]
  : π (Q = R) → π ((P ⇒ Q) = (P ⇒ R)) ≔
begin assume P Q R h; rewrite h; reflexivity end;

// Strip a known antecedent: π P → ((P ⇒ Q) = Q).
opaque symbol imp_known_drop [P Q : Prop]
  : π P → π ((P ⇒ Q) = Q) ≔
begin
  assume P Q hp;
  refine propExt _ _ _ _
  { assume hpq; refine hpq hp }
  { assume hq hp2; refine hq }
end;

// ============================================================
// Per-connective equality lemmas (§A.1–A.5, A.13)
// ============================================================

// AND1: ¬(P∧Q)⇒R = (¬Q⇒R) ∧ (¬P⇒R)
opaque symbol and1_eq [P Q R : Prop]
  : π ((¬ (P ∧ Q) ⇒ R) = ((¬ Q ⇒ R) ∧ (¬ P ⇒ R))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h; refine ∧ᵢ
      (λ hnq, h (λ hpq, hnq (∧ₑ₂ hpq)))
      (λ hnp, h (λ hpq, hnp (∧ₑ₁ hpq))) }
    { assume h hnpq;
      have hnpnq : π (¬ P ∨ ¬ Q) { refine =⇒ (deMorgan_∧ P Q) hnpq };
      refine ∨ₑ hnpnq _ _
      { assume hnp; refine ∧ₑ₂ h hnp }
      { assume hnq; refine ∧ₑ₁ h hnq } }
end;

// AND2: ¬(P∧Q) = (P⇒¬Q)
opaque symbol and2_eq [P Q : Prop]
  : π (¬ (P ∧ Q) = (P ⇒ ¬ Q)) ≔
begin
  assume P Q;
  refine propExt _ _ _ _
    { assume h1 hp hq; refine h1 (∧ᵢ hp hq) }
    { assume h1 h2; refine h1 (∧ₑ₁ h2) (∧ₑ₂ h2) }
end;

// AND3: (P∧Q)⇒R = (P⇒Q⇒R)
opaque symbol and3_eq [P Q R : Prop]
  : π (((P ∧ Q) ⇒ R) = (P ⇒ Q ⇒ R)) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h1 hp hq; refine h1 (∧ᵢ hp hq) }
    { assume h1 h2; refine h1 (∧ₑ₁ h2) (∧ₑ₂ h2) }
end;

// OR1: ¬(P∨Q)⇒R = (¬P⇒¬Q⇒R)
opaque symbol or1_eq [P Q R : Prop]
  : π ((¬ (P ∨ Q) ⇒ R) = (¬ P ⇒ (¬ Q ⇒ R))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h1 hnp hnq;
      have hnpq : π (¬ (P ∨ Q))
        { assume hpq; refine ∨ₑ hpq _ _
          { assume hp; refine hnp hp }
          { assume hq; refine hnq hq } };
      refine h1 hnpq }
    { assume h1 hnpq;
      have hnpnq : π (¬ P ∧ ¬ Q) { refine =⇒ (deMorgan_∨ P Q) hnpq };
      refine h1 (∧ₑ₁ hnpnq) (∧ₑ₂ hnpnq) }
end;

// OR2: ¬(P∨Q) = (¬Q ∧ ¬P)
opaque symbol or2_eq [P Q : Prop]
  : π (¬ (P ∨ Q) = (¬ Q ∧ ¬ P)) ≔
begin
  assume P Q;
  rewrite deMorgan_∨;
  rewrite ∧_com;
  reflexivity
end;

// OR3: (P∨Q)⇒R = (Q⇒R) ∧ (P⇒R)
opaque symbol or3_eq [P Q R : Prop]
  : π (((P ∨ Q) ⇒ R) = ((Q ⇒ R) ∧ (P ⇒ R))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h; refine ∧ᵢ (λ hq, h (∨ᵢ₂ hq)) (λ hp, h (∨ᵢ₁ hp)) }
    { assume h hpq; refine ∨ₑ hpq _ _
      { assume hp; refine ∧ₑ₂ h hp }
      { assume hq; refine ∧ₑ₁ h hq } }
end;

// OR4: P∨Q = (¬P⇒Q). P, Q explicit to avoid HO-unification issues.
opaque symbol or4_eq (P Q : Prop)
  : π ((P ∨ Q) = (¬ P ⇒ Q)) ≔
begin
  assume P Q;
  refine propExt _ _ _ _
    { assume hpq hnp; refine ∨ₑ hpq _ _
      { assume hp; refine ⊥ₑ (hnp hp) }
      { assume hq; refine hq } }
    { assume h1; refine ∨ₑ (em P) _ _
      { assume hp; refine ∨ᵢ₁ hp }
      { assume hnp; refine ∨ᵢ₂ (h1 hnp) } }
end;

// IMP1: ¬(P⇒Q)⇒R = (P⇒¬Q⇒R)
opaque symbol imp1_eq [P Q R : Prop]
  : π ((¬ (P ⇒ Q) ⇒ R) = (P ⇒ (¬ Q ⇒ R))) ≔
begin
  assume P Q R;
  rewrite ¬⇒=∧¬;
  refine propExt _ _ _ _
    { assume h1 hp hnq; refine h1 (∧ᵢ hp hnq) }
    { assume h1 h2; refine h1 (∧ₑ₁ h2) (∧ₑ₂ h2) }
end;

// IMP2: ¬(P⇒Q) = (¬Q ∧ P)
opaque symbol imp2_eq [P Q : Prop]
  : π (¬ (P ⇒ Q) = (¬ Q ∧ P)) ≔
begin
  assume P Q;
  rewrite ¬⇒=∧¬;
  rewrite ∧_com;
  reflexivity
end;

// IMP3: (P⇒Q)⇒R = (Q⇒R) ∧ (¬P⇒R)
opaque symbol imp3_eq [P Q R : Prop]
  : π (((P ⇒ Q) ⇒ R) = ((Q ⇒ R) ∧ (¬ P ⇒ R))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h; refine ∧ᵢ
      (λ hq, h (λ h0, hq))
      (λ hnp, h (λ hp, ⊥ₑ (hnp hp))) }
    { assume h hpq; refine ∨ₑ (em P) _ _
      { assume hp; refine ∧ₑ₁ h (hpq hp) }
      { assume hnp; refine ∧ₑ₂ h hnp } }
end;

// EQV1: ¬(P⇔Q)⇒R = (P⇒¬Q⇒R) ∧ (¬P⇒Q⇒R)
opaque symbol eqv1_eq [P Q R : Prop]
  : π ((¬ (P ⇔ Q) ⇒ R) = ((P ⇒ (¬ Q ⇒ R)) ∧ (¬ P ⇒ (Q ⇒ R)))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h; refine ∧ᵢ
      (λ hp hnq, h (λ heqv, hnq (∧ₑ₁ heqv hp)))
      (λ hnp hq, h (λ heqv, hnp (∧ₑ₂ heqv hq))) }
    { assume h hneqv;
      refine ∨ₑ (em P) _ _
      { assume hp; refine ∨ₑ (em Q) _ _
        { assume hq;
          have heqv : π (P ⇔ Q) { refine ∧ᵢ (λ h0, hq) (λ h0, hp) };
          refine ⊥ₑ (hneqv heqv) }
        { assume hnq; refine ∧ₑ₁ h hp hnq } }
      { assume hnp; refine ∨ₑ (em Q) _ _
        { assume hq; refine ∧ₑ₂ h hnp hq }
        { assume hnq;
          have heqv : π (P ⇔ Q)
            { refine ∧ᵢ (λ hp, ⊥ₑ (hnp hp)) (λ hq, ⊥ₑ (hnq hq)) };
          refine ⊥ₑ (hneqv heqv) } } }
end;

// EQV3: (P⇔Q)⇒R = (P⇒Q⇒R) ∧ (¬P⇒¬Q⇒R)
opaque symbol eqv3_eq [P Q R : Prop]
  : π (((P ⇔ Q) ⇒ R) = ((P ⇒ (Q ⇒ R)) ∧ (¬ P ⇒ (¬ Q ⇒ R)))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h; refine ∧ᵢ
      (λ hp hq, h (∧ᵢ (λ h0, hq) (λ h0, hp)))
      (λ hnp hnq, h (∧ᵢ
        (λ hp, ⊥ₑ (hnp hp))
        (λ hq, ⊥ₑ (hnq hq)))) }
    { assume h heqv;
      refine ∨ₑ (em P) _ _
      { assume hp;
        have hq : π Q { refine ∧ₑ₁ heqv hp };
        refine ∧ₑ₁ h hp hq }
      { assume hnp;
        refine ∨ₑ (em Q) _ _
        { assume hq;
          have hp : π P { refine ∧ₑ₂ heqv hq };
          refine ⊥ₑ (hnp hp) }
        { assume hnq; refine ∧ₑ₂ h hnp hnq } } }
end;

// NOT1: ¬¬P⇒R = (P⇒R)
opaque symbol not1_eq [P R : Prop]
  : π ((¬ ¬ P ⇒ R) = (P ⇒ R)) ≔
begin
  assume P R;
  refine propExt _ _ _ _
    { assume h1 hp; refine h1 (λ hnp, hnp hp) }
    { assume h1 hnnp; refine h1 (¬¬ₑ P hnnp) }
end;

// EVR3: (E=E)⇒P = P
opaque symbol evr3_eq [E : τ ι] [P : Prop]
  : π (((E = E) ⇒ P) = P) ≔
begin
  assume E P;
  refine propExt _ _ _ _
    { assume h1; refine h1 (eq_refl E) }
    { assume h1 h2; refine h1 }
end;

// ============================================================
// Special bridges (OPR1/OPR2, XST7/XST8, NRM1)
// ============================================================

// OPR1 bridge: (x=E ⇒ P x) = (x=E ⇒ P E). Holds pointwise: when x=E
// is true, both sides reduce to P E; when false, both are vacuously ⊤.
opaque symbol opr1_eq [E : τ ι] (P : τ ι → Prop) (x : τ ι)
  : π ((x = E ⇒ P x) = (x = E ⇒ P E)) ≔
begin
  assume E P x;
  refine propExt _ _ _ _
    { assume hyp hxe; have px : π (P x) { refine hyp hxe };
      rewrite left hxe; refine px }
    { assume hyp hxe; have pe : π (P E) { refine hyp hxe };
      rewrite hxe; refine pe }
end;

// OPR2 bridge: (E=x ⇒ P x) = (E=x ⇒ P E).
opaque symbol opr2_eq [E : τ ι] (P : τ ι → Prop) (x : τ ι)
  : π ((E = x ⇒ P x) = (E = x ⇒ P E)) ≔
begin
  assume E P x;
  refine propExt _ _ _ _
    { assume hyp hex; have px : π (P x) { refine hyp hex };
      rewrite hex; refine px }
    { assume hyp hex; have pe : π (P E) { refine hyp hex };
      rewrite left hex; refine pe }
end;

// XST7: ((∃-block, P) ⇒ R) = (∀-block, P ⇒ R)
opaque symbol xst7_eq [n] [P : Tuple n → Prop] [R : Prop]
  : π (((`?? v, P v) ⇒ R) = (`!! v, P v ⇒ R)) ≔
begin
  assume n P R;
  refine propExt _ _ _ _
    { assume hir; refine pi_to_!! _
        (λ v hPv, hir (pi_to_??_intro P v hPv)) }
    { assume hall hex; refine pi_to_??_elim P
        (λ v hpv, !!_to_pi (λ v, P v ⇒ R) hall v hpv) hex }
end;

// XST8: (∃-block, P) = ((∀-block, ¬P) ⇒ ⊥)
opaque symbol xst8_eq [n] [P : Tuple n → Prop]
  : π ((`?? v, P v) = ((`!! v, ¬ (P v)) ⇒ ⊥)) ≔
begin
  assume n P;
  refine propExt _ _ _ _
    { assume hex hall; refine pi_to_??_elim P
        (λ v hpv, !!_to_pi (λ v, ¬ (P v)) hall v hpv) hex }
    { assume hc; refine ¬¬ₑ _ (λ hne,
        hc (pi_to_!! (λ v, ¬ (P v))
              (λ v hpv, hne (pi_to_??_intro P v hpv)))) }
end;

// NRM1 bridge: ((♢_:Tuple n, P) ⇒ Q) = (P ⇒ Q) when P is x-free.
opaque symbol nrm1_eq [n] [P Q : Prop]
  : π (((`♢ _ : Tuple n, P) ⇒ Q) = (P ⇒ Q)) ≔
begin
  assume n P Q;
  have h1 : π ((`♢ _ : Tuple n, P) = P)
    { refine eq_trans (♢_eq_!! (λ _ : Tuple n, P)) (!!_const [n] P) };
  rewrite h1; reflexivity
end;

// ============================================================
// left_∧: left-fold combinator for AND4 chains
// ============================================================
// `left_∧ x y` left-folds x into the binary ∧-tree y, accumulating on
// the left.  Fires automatically and correctly at any chain depth:
//   left_∧ r (q ∧ p)       ↪ left_∧ (left_∧ r q) p ↪ (r ∧ q) ∧ p
//   left_∧ d ((c ∧ b) ∧ a) ↪ left_∧ (left_∧ d (c ∧ b)) a ↪ ((d ∧ c) ∧ b) ∧ a
sequential symbol left_∧ : τ o → τ o → τ o;
rule left_∧ $x ($a ∧ $b) ↪ left_∧ (left_∧ $x $a) $b
with left_∧ $x $y ↪ $x ∧ $y;

// ============================================================
// Res leaf
// ============================================================

symbol STOP_1 [P : Prop] : Res P
  ≔ mk_1 P (eq_refl P);

// ============================================================
// Res passthrough rules
// ============================================================

symbol AND2_1 [P Q : Prop]
  (r : Res (P ⇒ ¬ Q)) : Res (¬ (P ∧ Q))
  ≔ mk_1 (res_tm r) (eq_trans and2_eq (res_eq r));

symbol AND3_1 [P Q R : Prop]
  (r : Res (P ⇒ Q ⇒ R)) : Res ((P ∧ Q) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans and3_eq (res_eq r));

symbol OR1_1 [P Q R : Prop]
  (r : Res (¬ P ⇒ ¬ Q ⇒ R)) : Res (¬ (P ∨ Q) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans or1_eq (res_eq r));

symbol OR4_1 [P Q : Prop]
  (r : Res (¬ P ⇒ Q)) : Res (P ∨ Q)
  ≔ mk_1 (res_tm r) (eq_trans (or4_eq P Q) (res_eq r));

symbol NOT1_1 [P R : Prop]
  (r : Res (P ⇒ R)) : Res (¬ ¬ P ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans not1_eq (res_eq r));

symbol NOT2_1 [P : Prop]
  (r : Res P) : Res (¬ ¬ P)
  ≔ mk_1 (res_tm r) (eq_trans (¬¬ₑ_eq P) (res_eq r));

symbol IMP1_1 [P Q R : Prop]
  (r : Res (P ⇒ ¬ Q ⇒ R)) : Res (¬ (P ⇒ Q) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans imp1_eq (res_eq r));

symbol VR3_1 [P : Prop]
  (r : Res P) : Res (⊤ ⇒ P)
  ≔ mk_1 (res_tm r) (eq_trans (⊤⇒ P) (res_eq r));

symbol EVR2_1 [E : τ ι]
  (r : Res ⊥) : Res (¬ (E = E))
  ≔ mk_1 (res_tm r) (eq_trans (¬=_idem ι E) (res_eq r));

symbol EVR3_1 [E : τ ι] [P : Prop]
  (r : Res P) : Res ((E = E) ⇒ P)
  ≔ mk_1 (res_tm r) (eq_trans evr3_eq (res_eq r));


symbol OPR1_1 [E : τ ι] (P : τ ι → Prop) [x : τ ι]
  (r : Res (x = E ⇒ P E)) : Res (x = E ⇒ P x)
  ≔ mk_1 (res_tm r) (eq_trans (opr1_eq P x) (res_eq r));

symbol OPR2_1 [E : τ ι] (P : τ ι → Prop) [x : τ ι]
  (r : Res (E = x ⇒ P E)) : Res (E = x ⇒ P x)
  ≔ mk_1 (res_tm r) (eq_trans (opr2_eq P x) (res_eq r));

// ============================================================
// Res structural rules
// ============================================================

// IMP4_1: congruence of ⇒ on the right (P doesn't depend on context).
symbol IMP4_1 [P Q : Prop]
  (r : Res Q) : Res (P ⇒ Q)
  ≔ mk_1 (P ⇒ res_tm r) (imp_cong_r (res_eq r));

// Helpers used below.
opaque symbol imp_cong_l [P P' Q : Prop]
  : π (P = P') → π ((P ⇒ Q) = (P' ⇒ Q)) ≔
begin assume P P' Q h; rewrite h; reflexivity end;

opaque symbol leq_zero_eq [E F : τ ι]
  : π (E = F) → π ((E ≤ 𝟎) = (F ≤ 𝟎)) ≔
begin assume E F h; rewrite h; reflexivity end;

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

// IMP5_1: strip a known antecedent (hp : π P) — collapses the ⇒.
symbol IMP5_1 [P Q : Prop]
  (hp : π P) (r : Res Q) : Res (P ⇒ Q)
  ≔ mk_1 (res_tm r) (eq_trans (imp_known_drop hp) (res_eq r));

// ALL9_1: same shape as IMP4_1 — H ⇒ continuation.
symbol ALL9_1 [H Q : Prop]
  (r : Res Q) : Res (H ⇒ Q)
  ≔ mk_1 (H ⇒ res_tm r) (imp_cong_r (res_eq r));

// NRM1_1: strip constant ♢-binder.
symbol NRM1_1 [n] [P Q : Prop]
  (r : Res (P ⇒ Q)) : Res ((`♢ _ : Tuple n, P) ⇒ Q)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm1_eq n P Q) (res_eq r));

// ALL8_1: congruence under ∀-block.
symbol ALL8_1 [n] [P : Tuple n → Prop]
  (ρ : Π v : Tuple n, Res (P v)) : Res (`!! v, P v)
  ≔ mk_1 (`!! v, res_tm (ρ v))
           (!!_cong (λ v, res_eq (ρ v)));

// XST7_1: (∃-block, P) ⇒ R via (∀-block, P ⇒ R).
symbol XST7_1 [n] [P : Tuple n → Prop] [R : Prop]
  (r : Res (`!! v, P v ⇒ R)) : Res ((`?? v, P v) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans xst7_eq (res_eq r));

// XST8_1: ∃-block, P via ((∀-block, ¬P) ⇒ ⊥).
symbol XST8_1 [n] [P : Tuple n → Prop]
  (r : Res ((`!! v, ¬ (P v)) ⇒ ⊥)) : Res (`?? v, P v)
  ≔ mk_1 (res_tm r) (eq_trans xst8_eq (res_eq r));

// ALL7_1: branching quantifier — per-tuple Res chain ρ + continuation r.
//   Continuation premise uses `♢` (post-normalisation form per spec).
opaque symbol ALL7_1 [n] [P : Tuple n → Prop] [Q : Prop]
  (ρ : Π v : Tuple n, Res (P v))
  (r : Res ((`♢ v, res_tm (ρ v)) ⇒ Q))
  : Res ((`!! v, P v) ⇒ Q) ≔
begin
  assume n P Q ρ r;
  refine mk_1 (res_tm r) _;
  have h1 : π ((`!! v, P v) = (`♢ v, res_tm (ρ v)))
    { refine eq_trans (!!_cong (λ v, res_eq (ρ v)))
        (eq_sym (♢_eq_!! (λ v, res_tm (ρ v)))) };
  have h2 : π (((`!! v, P v) ⇒ Q) = ((`♢ v, res_tm (ρ v)) ⇒ Q))
    { rewrite h1; reflexivity };
  refine eq_trans h2 (res_eq r)
end;

// ============================================================
// Res branching rules (two children → conjunction normal form)
// ============================================================

symbol AND1_1 [P Q R : Prop]
  (r1 : Res (¬ Q ⇒ R)) (r2 : Res (¬ P ⇒ R))
  : Res (¬ (P ∧ Q) ⇒ R)
  ≔ mk_1 (res_tm r1 ∧ res_tm r2)
      (eq_trans and1_eq (conj_eq (res_eq r1) (res_eq r2)));

// AND4_1: (P ∧ Q) → (Q ∧ P) via ∧_com, then per-arg Res children.
// `left_∧` reduces (S1 ∧ S2) to its left-assoc tree definitionally.
symbol AND4_1 [P Q : Prop]
  (r1 : Res Q) (r2 : Res P) : Res (P ∧ Q)
  ≔ mk_1 (left_∧ (res_tm r1) (res_tm r2))
           (eq_trans (∧_com P Q) (conj_eq (res_eq r1) (res_eq r2)));

symbol OR2_1 [P Q : Prop]
  (r1 : Res (¬ Q)) (r2 : Res (¬ P)) : Res (¬ (P ∨ Q))
  ≔ mk_1 (res_tm r1 ∧ res_tm r2)
      (eq_trans or2_eq (conj_eq (res_eq r1) (res_eq r2)));

symbol OR3_1 [P Q R : Prop]
  (r1 : Res (Q ⇒ R)) (r2 : Res (P ⇒ R))
  : Res ((P ∨ Q) ⇒ R)
  ≔ mk_1 (res_tm r1 ∧ res_tm r2)
      (eq_trans or3_eq (conj_eq (res_eq r1) (res_eq r2)));

symbol IMP3_1 [P Q R : Prop]
  (r1 : Res (Q ⇒ R)) (r2 : Res (¬ P ⇒ R))
  : Res ((P ⇒ Q) ⇒ R)
  ≔ mk_1 (res_tm r1 ∧ res_tm r2)
      (eq_trans imp3_eq (conj_eq (res_eq r1) (res_eq r2)));

symbol IMP2_1 [P Q : Prop]
  (r1 : Res (¬ Q)) (r2 : Res P) : Res (¬ (P ⇒ Q))
  ≔ mk_1 (res_tm r1 ∧ res_tm r2)
      (eq_trans imp2_eq (conj_eq (res_eq r1) (res_eq r2)));

symbol EQV1_1 [P Q R : Prop]
  (r1 : Res (P ⇒ ¬ Q ⇒ R)) (r2 : Res (¬ P ⇒ Q ⇒ R))
  : Res (¬ (P ⇔ Q) ⇒ R)
  ≔ mk_1 (res_tm r1 ∧ res_tm r2)
      (eq_trans eqv1_eq (conj_eq (res_eq r1) (res_eq r2)));

symbol EQV3_1 [P Q R : Prop]
  (r1 : Res (P ⇒ Q ⇒ R)) (r2 : Res (¬ P ⇒ ¬ Q ⇒ R))
  : Res ((P ⇔ Q) ⇒ R)
  ≔ mk_1 (res_tm r1 ∧ res_tm r2)
      (eq_trans eqv3_eq (conj_eq (res_eq r1) (res_eq r2)));

// (Chain-exit operators ALL7_close / XST8_close have been folded
//  into the canonical ALL7 / XST8 in All.lp / Xst.lp respectively.)
