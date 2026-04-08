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
