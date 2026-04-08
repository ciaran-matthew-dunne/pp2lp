// Disjunction (§A.2) — shallow encoding
require open pp2lp.B;

// ---- Base rules ----

// OR1: H ⊢ ¬P ⇒ (¬Q ⇒ R) → H ⊢ ¬(P ∨ Q) ⇒ R
opaque symbol OR1 [P Q R]
  : π (¬ P ⇒ (¬ Q ⇒ R))
  → π (¬ (P ∨ Q) ⇒ R) ≔
begin
  assume P Q R h1 h2;
  have h : π (¬ P ∧ ¬ Q) {refine =⇒ (deMorgan_∨ P Q) h2};
  refine h1 (∧ₑ₁ h) (∧ₑ₂ h)
end;

// OR2: H ⊢ ¬Q; H ⊢ ¬P → H ⊢ ¬(P ∨ Q)
opaque symbol OR2 [P Q]
  : π (¬ Q)
  → π (¬ P)
  → π (¬ (P ∨ Q)) ≔
begin
  assume P Q hq hp hpq;
  refine ∨ₑ hpq _ _ {
    assume h; refine hp h
  } {
    assume h; refine hq h
  }
end;

// OR3: H ⊢ Q ⇒ R; H ⊢ P ⇒ R → H ⊢ (P ∨ Q) ⇒ R
opaque symbol OR3 [P Q R]
  : π (Q ⇒ R)
  → π (P ⇒ R)
  → π ((P ∨ Q) ⇒ R) ≔
begin
  assume P Q R hq hp hpq;
  refine ∨ₑ hpq _ _ {
    assume h; refine hp h
  } {
    assume h; refine hq h
  }
end;

// OR4: H ⊢ ¬P ⇒ Q → H ⊢ P ∨ Q
opaque symbol OR4 [P Q]
  : π (¬ P ⇒ Q)
  → π (P ∨ Q) ≔
begin
  assume P Q h1;
  refine ∨ₑ (em P) _ _ {
    assume hp; refine ∨ᵢ₁ hp
  } {
    assume hnp; refine ∨ᵢ₂ (h1 hnp)
  }
end;
