// Implication (§A.3) — shallow encoding
require open pp2lp.B;

// ---- Base rules ----

// IMP1: H ⊢ P ⇒ (¬Q ⇒ R) → H ⊢ ¬(P ⇒ Q) ⇒ R
opaque symbol IMP1 [P Q R]
  : π (P ⇒ (¬ Q ⇒ R))
  → π (¬ (P ⇒ Q) ⇒ R) ≔
begin
  assume P Q R h1 h2;
  have hp : π P {
    refine ¬¬ₑ P _;
    assume hnp;
    refine h2 (λ p, ⊥ₑ (hnp p))
  };
  have hnq : π (¬ Q) {
    assume hq;
    refine h2 (λ _, hq)
  };
  refine h1 hp hnq
end;

// IMP2: H ⊢ ¬Q; H ⊢ P → H ⊢ ¬(P ⇒ Q)
opaque symbol IMP2 [P Q]
  : π (¬ Q)
  → π P
  → π (¬ (P ⇒ Q)) ≔
begin
  assume P Q hnq hp hpq;
  refine hnq (hpq hp)
end;

// IMP3: H ⊢ Q ⇒ R; H ⊢ ¬P ⇒ R → H ⊢ (P ⇒ Q) ⇒ R
opaque symbol IMP3 [P Q R]
  : π (Q ⇒ R)
  → π (¬ P ⇒ R)
  → π ((P ⇒ Q) ⇒ R) ≔
begin
  assume P Q R hqr hnpr hpq;
  refine ∨ₑ (em P) _ _ {
    assume hp; refine hqr (hpq hp)
  } {
    assume hnp; refine hnpr hnp
  }
end;

// IMP4: H, P ⊢ Q → H ⊢ P ⇒ Q
opaque symbol IMP4 [P Q]
  : (π P → π Q)
  → π (P ⇒ Q) ≔
begin
  assume P Q h; refine h
end;

// IMP5: P is in H; H ⊢ Q → H ⊢ P ⇒ Q
opaque symbol IMP5 [P Q]
  : π Q
  → π (P ⇒ Q) ≔
begin
  assume P Q hq hp; refine hq
end;

// ---- Primed variants (equality-based) ----

// IMP1_1: pass-through. ¬(P⇒Q)⇒R = P⇒(¬Q⇒R).
opaque symbol IMP1_1 [P Q R S : Prop]
  : π ((P ⇒ (¬ Q ⇒ R)) = S)
  → π ((¬ (P ⇒ Q) ⇒ R) = S) ≔
begin
  assume P Q R S h;
  have eq : π ((¬ (P ⇒ Q) ⇒ R) = (P ⇒ (¬ Q ⇒ R)))
    { rewrite ¬⇒=∧¬;
      refine propExt _ _ _ _
      { assume h1 hp hnq; refine h1 (∧ᵢ hp hnq) }
      { assume h1 h2; refine h1 (∧ₑ₁ h2) (∧ₑ₂ h2) } };
  rewrite eq; refine h
end;

// IMP2_1: multi-premise. ¬(P⇒Q) = ¬Q ∧ P.
opaque symbol IMP2_1 [P Q S1 S2 : Prop]
  : π (¬ Q = S1)
  → π (P = S2)
  → π (¬ (P ⇒ Q) = (S1 ∧ S2)) ≔
begin
  assume P Q S1 S2 h1 h2;
  rewrite ¬⇒=∧¬;
  have eq : π ((P ∧ ¬ Q) = (¬ Q ∧ P))
    { refine ∧_com P (¬ Q) };
  rewrite eq; rewrite h1; rewrite h2; reflexivity
end;

// IMP3_1: multi-premise. (P⇒Q)⇒R = (Q⇒R) ∧ (¬P⇒R).
opaque symbol IMP3_1 [P Q R S1 S2 : Prop]
  : π ((Q ⇒ R) = S1)
  → π ((¬ P ⇒ R) = S2)
  → π (((P ⇒ Q) ⇒ R) = (S1 ∧ S2)) ≔
begin
  assume P Q R S1 S2 h1 h2;
  have eq : π (((P ⇒ Q) ⇒ R) = ((Q ⇒ R) ∧ (¬ P ⇒ R)))
    { refine propExt _ _ _ _
      { assume h; refine ∧ᵢ
        (λ hq, h (λ _, hq))
        (λ hnp, h (λ hp, ⊥ₑ (hnp hp))) }
      { assume h hpq; refine ∨ₑ (em P) _ _
        { assume hp; refine ∧ₑ₁ h (hpq hp) }
        { assume hnp; refine ∧ₑ₂ h hnp } } };
  rewrite eq; rewrite h1; rewrite h2; reflexivity
end;

// IMP4_1: structural. (P⇒Q) = (P⇒R) from Q = R under hypothesis P.
opaque symbol IMP4_1 [P Q R : Prop]
  : (π P → π (Q = R))
  → π ((P ⇒ Q) = (P ⇒ R)) ≔
begin
  assume P Q R h;
  refine propExt _ _ _ _
    { assume h1 hp; refine =⇒ (h hp) (h1 hp) }
    { assume h1 hp; refine =⇒ (eq_sym (h hp)) (h1 hp) }
end;

// IMP5_1: pass-through. P⇒Q from Q (P is known).
opaque symbol IMP5_1 [P Q S : Prop]
  : π P
  → π (Q = S)
  → π ((P ⇒ Q) = (P ⇒ S)) ≔
begin
  assume P Q S hp h;
  rewrite h; reflexivity
end;
