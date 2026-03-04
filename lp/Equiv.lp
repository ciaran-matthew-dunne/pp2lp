// Equivalence rules (spec §A.4)
require open pp2lp.B pp2lp.Eq pp2lp.Interp;

// ---- base rules ----------------

opaque symbol EQV1 [H P Q R]
  : (H ⊩ P ⇒ (¬ Q ⇒ R)) → (H ⊩ ¬ P ⇒ (Q ⇒ R))
  → (H ⊩ ¬ (P ⇔ Q) ⇒ R) ≔
begin
  assume H P Q R; simplify;
  assume one two h npq;
  apply ∨ₑ (em (sat vnil P))
  { assume hp;
    refine one h hp (λ hq, npq (∧ᵢ (λ _, hq) (λ _, hp))) }
  { assume hnp;
    apply ∨ₑ (em (sat vnil Q))
    { assume hq; refine two h hnp hq }
    { assume hnq; refine one h (¬¬ₑ _ (λ np, npq (∧ᵢ (λ hp, ⊥ₑ (np hp)) (λ hq, ⊥ₑ (hnq hq))))) hnq } }
end;

opaque symbol EQV2 [H P Q]
  : (H ⊩ P ⇒ ¬ Q) → (H ⊩ ¬ Q ⇒ P) → (H ⊩ ¬ (P ⇔ Q)) ≔
begin
  assume H P Q; simplify; assume one two h pq;
  set pq1 ≔ ∧ₑ₁ pq; set pq2 ≔ ∧ₑ₂ pq;
  apply ∨ₑ (em (sat vnil Q))
  { assume hq; refine one h (pq2 hq) hq }
  { assume hnq; refine one h (two h hnq) (pq1 (two h hnq)) }
end;

opaque symbol EQV3 [H P Q R]
  : (H ⊩ P ⇒ (Q ⇒ R)) → (H ⊩ ¬ P ⇒ (¬ Q ⇒ R))
  → (H ⊩ (P ⇔ Q) ⇒ R) ≔
begin
  assume H P Q R; simplify; assume one two h pq;
  set pq1 ≔ ∧ₑ₁ pq; set pq2 ≔ ∧ₑ₂ pq;
  apply ∨ₑ (em (sat vnil P))
  { assume hp; refine one h hp (pq1 hp) }
  { assume hnp; refine two h hnp (λ hq, ⊥ₑ (hnp (pq2 hq))) }
end;

opaque symbol EQV4 [H P Q]
  : (H ⊩ P ⇒ Q) → (H ⊩ Q ⇒ P) → (H ⊩ P ⇔ Q) ≔
begin
  assume H P Q; simplify; assume one two h;
  refine ∧ᵢ (one h) (two h)
end;

// ---- primed (result-producing) variants ----------------

// EQV1': two antecedents → Schema 2.
symbol EQV1' [H P Q R]
  : Res (H ⟝ P ⇒ (¬ Q ⇒ R)) → Res (H ⟝ ¬ P ⇒ (Q ⇒ R))
  → Res (H ⟝ ¬ (P ⇔ Q) ⇒ R)
≔ λ ρ₁ ρ₂, result (obtain ρ₁ ∧ obtain ρ₂);

// EQV2': two antecedents → Schema 2.
symbol EQV2' [H P Q]
  : Res (H ⟝ P ⇒ ¬ Q) → Res (H ⟝ ¬ Q ⇒ P) → Res (H ⟝ ¬ (P ⇔ Q))
≔ λ ρ₁ ρ₂, result (obtain ρ₁ ∧ obtain ρ₂);

// EQV3': two antecedents → Schema 2.
symbol EQV3' [H P Q R]
  : Res (H ⟝ P ⇒ (Q ⇒ R)) → Res (H ⟝ ¬ P ⇒ (¬ Q ⇒ R))
  → Res (H ⟝ (P ⇔ Q) ⇒ R)
≔ λ ρ₁ ρ₂, result (obtain ρ₁ ∧ obtain ρ₂);

// EQV4': two antecedents → Schema 2.
symbol EQV4' [H P Q]
  : Res (H ⟝ P ⇒ Q) → Res (H ⟝ Q ⇒ P) → Res (H ⟝ P ⇔ Q)
≔ λ ρ₁ ρ₂, result (obtain ρ₁ ∧ obtain ρ₂);
