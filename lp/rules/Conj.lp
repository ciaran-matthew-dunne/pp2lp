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

// ---- Primed variants (equality-based) ----

// AND1_1: multi-premise, rewrites ¬(P∧Q)⇒R = (¬Q⇒R) ∧ (¬P⇒R).
opaque symbol AND1_1 [P Q R S1 S2 : Prop]
  : π ((¬ Q ⇒ R) = S1)
  → π ((¬ P ⇒ R) = S2)
  → π ((¬ (P ∧ Q) ⇒ R) = (S1 ∧ S2)) ≔
begin
  assume P Q R S1 S2 h1 h2;
  have eq : π ((¬ (P ∧ Q) ⇒ R) = ((¬ Q ⇒ R) ∧ (¬ P ⇒ R)))
    { refine propExt _ _ _ _
      { assume h; refine ∧ᵢ
        (λ hnq, h (λ hpq, hnq (∧ₑ₂ hpq)))
        (λ hnp, h (λ hpq, hnp (∧ₑ₁ hpq))) }
      { assume h hnpq;
        have hnpnq : π (¬ P ∨ ¬ Q) { refine =⇒ (deMorgan_∧ P Q) hnpq };
        refine ∨ₑ hnpnq _ _
        { assume hnp; refine ∧ₑ₂ h hnp }
        { assume hnq; refine ∧ₑ₁ h hnq } } };
  rewrite eq; rewrite h1; rewrite h2; reflexivity
end;

// AND2_1: pass-through. ¬(P∧Q) = (P ⇒ ¬Q).
opaque symbol AND2_1 [P Q S : Prop]
  : π ((P ⇒ ¬ Q) = S)
  → π (¬ (P ∧ Q) = S) ≔
begin
  assume P Q S h;
  have eq : π (¬ (P ∧ Q) = (P ⇒ ¬ Q))
    { refine propExt _ _ _ _
      { assume h1 hp hq; refine h1 (∧ᵢ hp hq) }
      { assume h1 h2; refine h1 (∧ₑ₁ h2) (∧ₑ₂ h2) } };
  rewrite eq; refine h
end;

// AND3_1: pass-through. (P∧Q)⇒R = P⇒Q⇒R.
opaque symbol AND3_1 [P Q R S : Prop]
  : π ((P ⇒ Q ⇒ R) = S)
  → π (((P ∧ Q) ⇒ R) = S) ≔
begin
  assume P Q R S h;
  have eq : π (((P ∧ Q) ⇒ R) = (P ⇒ Q ⇒ R))
    { refine propExt _ _ _ _
      { assume h1 hp hq; refine h1 (∧ᵢ hp hq) }
      { assume h1 h2; refine h1 (∧ₑ₁ h2) (∧ₑ₂ h2) } };
  rewrite eq; refine h
end;

// AND4_1: multi-premise. P∧Q = S1 ∧ S2 (rewrites under ∧).
opaque symbol AND4_1 [P Q S1 S2 : Prop]
  : π (Q = S1)
  → π (P = S2)
  → π ((P ∧ Q) = (S1 ∧ S2)) ≔
begin
  assume P Q S1 S2 h1 h2;
  rewrite ∧_com; rewrite h1; rewrite h2; reflexivity
end;

// AND5_1: equality-based modus ponens within a conjunction.
// Forward/backward functions convert between C and C'.
opaque symbol AND5_1 [C C' r s : Prop]
  : (π C → π C')
  → (π C' → π C)
  → π ((C' ⇒ r) = s)
  → π ((C ⇒ r) = s) ≔
begin
  assume C C' r s fwd bwd heq;
  have eq : π ((C ⇒ r) = (C' ⇒ r))
    { refine propExt _ _ _ _
      { assume hcr hc'; refine hcr (bwd hc') }
      { assume hc'r hc; refine hc'r (fwd hc) } };
  rewrite eq; refine heq
end;
