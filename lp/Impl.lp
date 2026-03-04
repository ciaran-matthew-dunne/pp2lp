// Implication rules (spec §A.3)
require open pp2lp.B pp2lp.Eq pp2lp.Interp;

// ---- base rules ----------------

// IMP1: not yet encoded as base rule.

opaque symbol IMP2 [H P Q]
  : (H ⊩ ¬ Q) → (H ⊩ P) → (H ⊩ ¬ (P ⇒ Q)) ≔
begin
  assume H P Q; simplify; assume one two h p;
  refine (one h) (p (two h))
end;

opaque symbol IMP3 [H P Q R]
  : (H ⊩ Q ⇒ R) → (H ⊩ (¬ P) ⇒ R) → (H ⊩ (P ⇒ Q) ⇒ R) ≔
begin
  assume H P Q R; simplify; print; assume one two h pq;
  apply ∨ₑ (em (sat vnil P))
  { assume hp; refine one h (pq hp) }
  { assume hnp; refine two h hnp }
end;

opaque symbol IMP4 [H P Q]
  : ((H ∷ P) ⊩ Q) → (H ⊩ P ⇒ Q) ≔
begin
  assume H P Q; assume hp h p;
  refine hp (∧ᵢ h p)
end;

// IMP5 — propositional version.
opaque symbol IMP5p [H P Q]
  : (π (sem vnil H) → π (sat vnil P)) → (H ⊩ Q) → (H ⊩ P ⇒ Q) ≔
begin
  assume H P Q lookup one; simplify; assume h p;
  refine one h
end;

// IMP5 — computational wrapper.
symbol IMP5 [H P Q]
  : ⁇ (P dans H) → (H ⊩ Q) → (H ⊩ P ⇒ Q);

// ---- primed (result-producing) variants ----------------

// IMP1': one antecedent → Schema 1.
symbol IMP1' [H P Q R]
  : Res (H ⟝ P ⇒ (¬ Q ⇒ R)) → Res (H ⟝ ¬ (P ⇒ Q) ⇒ R)
≔ λ ρ, result (obtain ρ);

// IMP2': two antecedents → Schema 2.
symbol IMP2' [H P Q]
  : Res (H ⟝ ¬ Q) → Res (H ⟝ P) → Res (H ⟝ ¬ (P ⇒ Q))
≔ λ ρ₁ ρ₂, result (obtain ρ₁ ∧ obtain ρ₂);

// IMP3': two antecedents → Schema 2.
symbol IMP3' [H P Q R]
  : Res (H ⟝ Q ⇒ R) → Res (H ⟝ ¬ P ⇒ R) → Res (H ⟝ (P ⇒ Q) ⇒ R)
≔ λ ρ₁ ρ₂, result (obtain ρ₁ ∧ obtain ρ₂);

// IMP4': special — (H, P ⊢ Q) ⇝ R → result = P ⇒ R
symbol IMP4' [H P Q]
  : Res ((H ∷ P) ⟝ Q) → Res (H ⟝ P ⇒ Q)
≔ λ ρ, result (P ⇒ obtain ρ);

// IMP5': Schema 1 (one antecedent: H ⊢ Q).
symbol IMP5' [H P Q]
  : ⁇ (P dans H) → Res (H ⟝ Q) → Res (H ⟝ P ⇒ Q)
≔ λ _ ρ, result (obtain ρ);
