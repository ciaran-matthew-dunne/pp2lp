// Equivalence (§A.4) — shallow encoding
require open pp2lp.B pp2lp.Quant pp2lp.rules.Res;

// EQV1: H ⊢ P ⇒ (¬Q ⇒ R); H ⊢ ¬P ⇒ (Q ⇒ R) → H ⊢ ¬(P ⇔ Q) ⇒ R
opaque symbol EQV1 [P Q R]
  : π (P ⇒ (¬ Q ⇒ R))
  → π (¬ P ⇒ (Q ⇒ R))
  → π (¬ (P ⇔ Q) ⇒ R) ≔
begin
  assume P Q R h1 h2 h3;
  refine ∨ₑ (em P) _ _ {
    assume hp;
    refine ∨ₑ (em Q) _ _ {
      assume hq;
      have heqv : π (P ⇔ Q) {
        refine ∧ᵢ (λ _, hq) (λ _, hp)
      };
      refine ⊥ₑ (h3 heqv)
    } {
      assume hnq; refine h1 hp hnq
    }
  } {
    assume hnp;
    refine ∨ₑ (em Q) _ _ {
      assume hq; refine h2 hnp hq
    } {
      assume hnq;
      have heqv : π (P ⇔ Q) {
        refine ∧ᵢ (λ hp, ⊥ₑ (hnp hp)) (λ hq, ⊥ₑ (hnq hq))
      };
      refine ⊥ₑ (h3 heqv)
    }
  }
end;

// EQV2: H ⊢ P ⇒ ¬Q; H ⊢ ¬Q ⇒ P → H ⊢ ¬(P ⇔ Q)
opaque symbol EQV2 [P Q]
  : π (P ⇒ ¬ Q)
  → π (¬ Q ⇒ P)
  → π (¬ (P ⇔ Q)) ≔
begin
  assume P Q h1 h2 h3;
  have h3a : π (P ⇒ Q) {refine ∧ₑ₁ h3};
  have h3b : π (Q ⇒ P) {refine ∧ₑ₂ h3};
  refine ∨ₑ (em Q) _ _ {
    assume hq;
    have hp : π P {refine h3b hq};
    have hnq : π (¬ Q) {refine h1 hp};
    refine hnq hq
  } {
    assume hnq;
    have hp : π P {refine h2 hnq};
    have hq : π Q {refine h3a hp};
    refine hnq hq
  }
end;

// EQV3: H ⊢ P ⇒ (Q ⇒ R); H ⊢ ¬P ⇒ (¬Q ⇒ R) → H ⊢ (P ⇔ Q) ⇒ R
opaque symbol EQV3 [P Q R]
  : π (P ⇒ (Q ⇒ R))
  → π (¬ P ⇒ (¬ Q ⇒ R))
  → π ((P ⇔ Q) ⇒ R) ≔
begin
  assume P Q R h1 h2 h3;
  have h3a : π (P ⇒ Q) {refine ∧ₑ₁ h3};
  have h3b : π (Q ⇒ P) {refine ∧ₑ₂ h3};
  refine ∨ₑ (em P) _ _ {
    assume hp;
    have hq : π Q {refine h3a hp};
    refine h1 hp hq
  } {
    assume hnp;
    refine ∨ₑ (em Q) _ _ {
      assume hq;
      have hp : π P {refine h3b hq};
      refine ⊥ₑ (hnp hp)
    } {
      assume hnq; refine h2 hnp hnq
    }
  }
end;

// EQV4: H ⊢ P ⇒ Q; H ⊢ Q ⇒ P → H ⊢ P ⇔ Q
opaque symbol EQV4 [P Q]
  : π (P ⇒ Q)
  → π (Q ⇒ P)
  → π (P ⇔ Q) ≔
begin
  assume P Q h1 h2;
  refine ∧ᵢ h1 h2
end;

// ---- `_1` (Result-form) variants — §8.13 ----

// EQV1_1: Schema 2 — combine.
symbol EQV1_1 [P Q R : Prop]
  (r1 : Res (P ⇒ ¬ Q ⇒ R)) (r2 : Res (¬ P ⇒ Q ⇒ R))
  : Res (¬ (P ⇔ Q) ⇒ R)
  ≔ mk_res (concat (res_ts r1) (res_ts r2))
      (eq_trans eqv1_eq
        (eq_trans (conj_eq (res_eq r1) (res_eq r2))
                  (conj_concat_eq (res_ts r1) (res_ts r2))));

// EQV2_1: Schema 2 — combine.
symbol EQV2_1 [P Q : Prop]
  (r1 : Res (P ⇒ ¬ Q)) (r2 : Res (¬ Q ⇒ P))
  : Res (¬ (P ⇔ Q))
  ≔ mk_res (concat (res_ts r1) (res_ts r2))
      (eq_trans eqv2_eq
        (eq_trans (conj_eq (res_eq r1) (res_eq r2))
                  (conj_concat_eq (res_ts r1) (res_ts r2))));

// EQV3_1: Schema 2 — combine.
symbol EQV3_1 [P Q R : Prop]
  (r1 : Res (P ⇒ Q ⇒ R)) (r2 : Res (¬ P ⇒ ¬ Q ⇒ R))
  : Res ((P ⇔ Q) ⇒ R)
  ≔ mk_res (concat (res_ts r1) (res_ts r2))
      (eq_trans eqv3_eq
        (eq_trans (conj_eq (res_eq r1) (res_eq r2))
                  (conj_concat_eq (res_ts r1) (res_ts r2))));

// EQV4_1: Schema 2 — combine.
symbol EQV4_1 [P Q : Prop]
  (r1 : Res (P ⇒ Q)) (r2 : Res (Q ⇒ P))
  : Res (P ⇔ Q)
  ≔ mk_res (concat (res_ts r1) (res_ts r2))
      (eq_trans eqv4_eq
        (eq_trans (conj_eq (res_eq r1) (res_eq r2))
                  (conj_concat_eq (res_ts r1) (res_ts r2))));
