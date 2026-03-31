// Equivalence (§A.4) — shallow encoding
require open pp2lp.B;

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

// ---- Primed variants (equality-based) ----

// EQV1_1: multi-premise, computes ¬(P⇔Q)⇒R = (P⇒(¬Q⇒R)) ∧ (¬P⇒(Q⇒R)).
opaque symbol EQV1_1 [P Q R S1 S2 : Prop]
  : π ((P ⇒ (¬ Q ⇒ R)) = S1)
  → π ((¬ P ⇒ (Q ⇒ R)) = S2)
  → π ((¬ (P ⇔ Q) ⇒ R) = (S1 ∧ S2)) ≔
begin
  assume P Q R S1 S2 h1 h2;
  have eq : π ((¬ (P ⇔ Q) ⇒ R) = ((P ⇒ (¬ Q ⇒ R)) ∧ (¬ P ⇒ (Q ⇒ R))))
    { refine propExt _ _ _ _
      { assume h; refine ∧ᵢ
        (λ hp hnq, h (λ heqv, hnq (∧ₑ₁ heqv hp)))
        (λ hnp hq, h (λ heqv, hnp (∧ₑ₂ heqv hq))) }
      { assume h hneqv;
        refine ∨ₑ (em P) _ _
        { assume hp; refine ∨ₑ (em Q) _ _
          { assume hq;
            have heqv : π (P ⇔ Q) { refine ∧ᵢ (λ _, hq) (λ _, hp) };
            refine ⊥ₑ (hneqv heqv) }
          { assume hnq; refine ∧ₑ₁ h hp hnq } }
        { assume hnp; refine ∨ₑ (em Q) _ _
          { assume hq; refine ∧ₑ₂ h hnp hq }
          { assume hnq;
            have heqv : π (P ⇔ Q)
              { refine ∧ᵢ (λ hp, ⊥ₑ (hnp hp)) (λ hq, ⊥ₑ (hnq hq)) };
            refine ⊥ₑ (hneqv heqv) } } } };
  rewrite eq; rewrite h1; rewrite h2; reflexivity
end;

// EQV2_1: multi-premise, computes ¬(P⇔Q) = (P⇒¬Q) ∧ (¬Q⇒P).
opaque symbol EQV2_1 [P Q S1 S2 : Prop]
  : π ((P ⇒ ¬ Q) = S1)
  → π ((¬ Q ⇒ P) = S2)
  → π (¬ (P ⇔ Q) = (S1 ∧ S2)) ≔
begin
  assume P Q S1 S2 h1 h2;
  have eq : π (¬ (P ⇔ Q) = ((P ⇒ ¬ Q) ∧ (¬ Q ⇒ P)))
    { refine propExt _ _ _ _
      { assume hneqv; refine ∧ᵢ
        (λ hp hq, hneqv (∧ᵢ (λ _, hq) (λ _, hp)))
        (λ hnq, ¬¬ₑ P (λ hnp, hneqv (∧ᵢ
          (λ hp, ⊥ₑ (hnp hp))
          (λ hq, ⊥ₑ (hnq hq))))) }
      { assume h heqv;
        have hpnq : π (P ⇒ ¬ Q) { refine ∧ₑ₁ h };
        have hnqp : π (¬ Q ⇒ P) { refine ∧ₑ₂ h };
        refine ∨ₑ (em Q) _ _
        { assume hq;
          have hp : π P { refine ∧ₑ₂ heqv hq };
          refine hpnq hp hq }
        { assume hnq;
          have hp : π P { refine hnqp hnq };
          have hq : π Q { refine ∧ₑ₁ heqv hp };
          refine hnq hq } } };
  rewrite eq; rewrite h1; rewrite h2; reflexivity
end;

// EQV3_1: multi-premise, computes (P⇔Q)⇒R = (P⇒(Q⇒R)) ∧ (¬P⇒(¬Q⇒R)).
opaque symbol EQV3_1 [P Q R S1 S2 : Prop]
  : π ((P ⇒ (Q ⇒ R)) = S1)
  → π ((¬ P ⇒ (¬ Q ⇒ R)) = S2)
  → π (((P ⇔ Q) ⇒ R) = (S1 ∧ S2)) ≔
begin
  assume P Q R S1 S2 h1 h2;
  have eq : π (((P ⇔ Q) ⇒ R) = ((P ⇒ (Q ⇒ R)) ∧ (¬ P ⇒ (¬ Q ⇒ R))))
    { refine propExt _ _ _ _
      { assume h; refine ∧ᵢ
        (λ hp hq, h (∧ᵢ (λ _, hq) (λ _, hp)))
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
          { assume hnq; refine ∧ₑ₂ h hnp hnq } } } };
  rewrite eq; rewrite h1; rewrite h2; reflexivity
end;

// EQV4_1: multi-premise, computes P⇔Q = (P⇒Q) ∧ (Q⇒P).
opaque symbol EQV4_1 [P Q S1 S2 : Prop]
  : π ((P ⇒ Q) = S1)
  → π ((Q ⇒ P) = S2)
  → π ((P ⇔ Q) = (S1 ∧ S2)) ≔
begin
  assume P Q S1 S2 h1 h2;
  have eq : π ((P ⇔ Q) = ((P ⇒ Q) ∧ (Q ⇒ P)))
    { refine propExt _ _ _ _
      { assume h; refine h }
      { assume h; refine h } };
  rewrite eq; rewrite h1; rewrite h2; reflexivity
end;
