// Conjunction (§A.1) — shallow encoding
require open pp2lp.B;

// ---- Base rules ----

// AND1: H ⊢ ¬Q ⇒ R; H ⊢ ¬P ⇒ R → H ⊢ ¬(P ∧ Q) ⇒ R
opaque symbol AND1 [P Q R]
  : π (¬ Q ⇒ R)
  → π (¬ P ⇒ R)
  → π (¬ (P ∧ Q) ⇒ R) ≔
begin
  assume P Q R h1 h2 h3;
  have h : π (¬ P ∨ ¬ Q)
    { refine =⇒ (deMorgan_∧ P Q) h3 };
  refine ∨ₑ h _ _
    { assume hnp; refine h2 hnp }
    { assume hnq; refine h1 hnq }
end;

// AND2: H ⊢ P ⇒ ¬Q → H ⊢ ¬(P ∧ Q)
opaque symbol AND2 [P Q]
  : π (P ⇒ ¬ Q)
  → π (¬ (P ∧ Q)) ≔
begin
  assume P Q h1 h2;
  refine h1 (∧ₑ₁ h2) (∧ₑ₂ h2)
end;

// AND3: H ⊢ P ⇒ (Q ⇒ R) → H ⊢ (P ∧ Q) ⇒ R
opaque symbol AND3 [P Q R]
  : π (P ⇒ (Q ⇒ R))
  → π ((P ∧ Q) ⇒ R) ≔
begin
  assume P Q R h1 h2;
  refine h1 (∧ₑ₁ h2) (∧ₑ₂ h2)
end;

// AND4: H ⊢ Q; H ⊢ P → H ⊢ P ∧ Q
opaque symbol AND4 [P Q]
  : π Q
  → π P
  → π (P ∧ Q) ≔
begin
  assume P Q h1 h2;
  refine ∧ᵢ h2 h1
end;

// AND5: modus ponens within a conjunction.
// The caller supplies a forward function that rebuilds the conjunction
// with (A ⇒ B) at position j replaced by B (using ∧ₑ₁/∧ₑ₂/∧ᵢ).
opaque symbol AND5 [C C' r : Prop]
  : (π C → π C')
  → π (C' ⇒ r)
  → π (C ⇒ r) ≔
begin
  assume C C' r fwd hsub hc;
  refine hsub (fwd hc)
end;
