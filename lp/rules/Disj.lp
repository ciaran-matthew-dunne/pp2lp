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

// ---- Primed variants (equality-based) ----

// OR1_1: pass-through. ¬(P∨Q)⇒R = ¬P⇒(¬Q⇒R).
opaque symbol OR1_1 [P Q R S : Prop]
  : π ((¬ P ⇒ (¬ Q ⇒ R)) = S)
  → π ((¬ (P ∨ Q) ⇒ R) = S) ≔
begin
  assume P Q R S h;
  have eq : π ((¬ (P ∨ Q) ⇒ R) = (¬ P ⇒ (¬ Q ⇒ R)))
    { refine propExt _ _ _ _
      { assume h1 hnp hnq;
        have hnpq : π (¬ (P ∨ Q))
          { assume hpq; refine ∨ₑ hpq _ _
            { assume hp; refine hnp hp }
            { assume hq; refine hnq hq } };
        refine h1 hnpq }
      { assume h1 hnpq;
        have hnpnq : π (¬ P ∧ ¬ Q) { refine =⇒ (deMorgan_∨ P Q) hnpq };
        refine h1 (∧ₑ₁ hnpnq) (∧ₑ₂ hnpnq) } };
  rewrite eq; refine h
end;

// OR2_1: multi-premise. ¬(P∨Q) = ¬P ∧ ¬Q.
opaque symbol OR2_1 [P Q S1 S2 : Prop]
  : π (¬ Q = S1)
  → π (¬ P = S2)
  → π (¬ (P ∨ Q) = (S1 ∧ S2)) ≔
begin
  assume P Q S1 S2 h1 h2;
  rewrite deMorgan_∨;
  rewrite ∧_com;
  rewrite h1; rewrite h2; reflexivity
end;

// OR3_1: multi-premise. (P∨Q)⇒R = (Q⇒R) ∧ (P⇒R).
opaque symbol OR3_1 [P Q R S1 S2 : Prop]
  : π ((Q ⇒ R) = S1)
  → π ((P ⇒ R) = S2)
  → π (((P ∨ Q) ⇒ R) = (S1 ∧ S2)) ≔
begin
  assume P Q R S1 S2 h1 h2;
  have eq : π (((P ∨ Q) ⇒ R) = ((Q ⇒ R) ∧ (P ⇒ R)))
    { refine propExt _ _ _ _
      { assume h; refine ∧ᵢ (λ hq, h (∨ᵢ₂ hq)) (λ hp, h (∨ᵢ₁ hp)) }
      { assume h hpq; refine ∨ₑ hpq _ _
        { assume hp; refine ∧ₑ₂ h hp }
        { assume hq; refine ∧ₑ₁ h hq } } };
  rewrite eq; rewrite h1; rewrite h2; reflexivity
end;

// OR4_1: pass-through. P∨Q = ¬P⇒Q.
opaque symbol OR4_1 [P Q S : Prop]
  : π ((¬ P ⇒ Q) = S)
  → π ((P ∨ Q) = S) ≔
begin
  assume P Q S h;
  have eq : π ((P ∨ Q) = (¬ P ⇒ Q))
    { refine propExt _ _ _ _
      { assume hpq hnp; refine ∨ₑ hpq _ _
        { assume hp; refine ⊥ₑ (hnp hp) }
        { assume hq; refine hq } }
      { assume h1; refine ∨ₑ (em P) _ _
        { assume hp; refine ∨ᵢ₁ hp }
        { assume hnp; refine ∨ᵢ₂ (h1 hnp) } } };
  rewrite eq; refine h
end;
