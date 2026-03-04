// Disjunction rules (spec §A.2)
require open pp2lp.B pp2lp.Eq pp2lp.Interp;

// ---- base rules ----------------

opaque symbol OR1 [H P Q R]
  : (H ⊩ ¬ P ⇒ (¬ Q ⇒ R)) → (H ⊩ ¬ (P ∨ Q) ⇒ R) ≔
begin
  assume H P Q R; simplify; assume one h npq;
  refine one h (λ hp, npq (∨ᵢ₁ hp)) (λ hq, npq (∨ᵢ₂ hq))
end;

opaque symbol OR2 [H P Q]
  : (H ⊩ ¬ Q) → (H ⊩ ¬ P) → (H ⊩ ¬ (P ∨ Q)) ≔
begin
  assume H P Q; simplify; assume one two h pq;
  apply ∨ₑ pq
  { assume hp; refine two h hp }
  { assume hq; refine one h hq }
end;

// OR3, OR4: not yet encoded as base rules.

// ---- primed (result-producing) variants ----------------

// OR1': one antecedent → Schema 1.
symbol OR1' [H P Q R]
  : Res (H ⟝ ¬ P ⇒ (¬ Q ⇒ R)) → Res (H ⟝ ¬ (P ∨ Q) ⇒ R)
≔ λ ρ, result (obtain ρ);

// OR2': two antecedents → Schema 2.
symbol OR2' [H P Q]
  : Res (H ⟝ ¬ Q) → Res (H ⟝ ¬ P) → Res (H ⟝ ¬ (P ∨ Q))
≔ λ ρ₁ ρ₂, result (obtain ρ₁ ∧ obtain ρ₂);

// OR3': two antecedents → Schema 2.
symbol OR3' [H P Q R]
  : Res (H ⟝ Q ⇒ R) → Res (H ⟝ P ⇒ R) → Res (H ⟝ (P ∨ Q) ⇒ R)
≔ λ ρ₁ ρ₂, result (obtain ρ₁ ∧ obtain ρ₂);

// OR4': one antecedent → Schema 1.
symbol OR4' [H P Q]
  : Res (H ⟝ ¬ P ⇒ Q) → Res (H ⟝ P ∨ Q)
≔ λ ρ, result (obtain ρ);
