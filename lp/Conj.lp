require open pp2lp.B pp2lp.Eq pp2lp.Interp;

// induction principle on hyp-lists (moved from PP.lp)
symbol Hyp_ind (M : Hyp → Prop)
  : π (M ⦳)
  → (Π H, π (M H) → Π Q, π (M (H ∷ Q)))
  → Π H, π (M H) ≔
begin
  assume M base step;
  induction
  { refine base }
  { assume H ih Q; refine step H ih Q }
end;

// soundness of conjunction containment check.
symbol contient_sound [N C]
  : ⁇ (N contient C) → (π (sat vnil C) → π (sat vnil N));

// soundness of conjunction removal.
symbol retirer_sound [N C]
  : ⁇ (N contient C) → (π (sat vnil C) → π (sat vnil (retirer N C)));


// ---- conjunction (spec §A.1) ----------------
opaque symbol AND1 [H P Q R]
  : (H ⊩ ¬ Q ⇒ R) → (H ⊩ ¬ P ⇒ R) → (H ⊩ ¬ (P ∧ Q) ⇒ R) ≔
begin
  assume H P Q R; simplify;
  assume one two h npq;
  apply ∨ₑ (em (sat vnil P))
  { assume hp; refine one h (λ hq, npq (∧ᵢ hp hq)) }
  { assume hnp; refine two h hnp }
end;

opaque symbol AND2 [H P Q]
  : (H ⊩ P ⇒ ¬ Q) → (H ⊩ ¬ (P ∧ Q)) ≔
begin
  assume H P Q; simplify;
  assume one h pq;
  refine one h (∧ₑ₁ pq) (∧ₑ₂ pq)
end;

opaque symbol AND3 [H P Q R]
  : (H ⊩ P ⇒ (Q ⇒ R)) → (H ⊩ (P ∧ Q) ⇒ R) ≔
begin
  assume H P Q R; simplify;
  assume one h pq;
  refine one h (∧ₑ₁ pq) (∧ₑ₂ pq)
end;


opaque symbol AND4 [H P Q]
  : (H ⊩ Q) → (H ⊩ P) → (H ⊩ P ∧ Q) ≔
begin
  assume H P Q; simplify;
  assume one two h;
  refine ∧ᵢ (two h) (one h)
end;

// AND5 — to be implemented.
// AND5 | P ∧ ··· contains A; H ⊢ P ∧ ··· ∧ B ∧ ··· ⇒ R | H ⊢ P ∧ ··· ∧ (A ⇒ B) ∧ ··· ⇒ R

// ---- primed (result-producing) variants ----------------

// AND1': two antecedents → Schema 2.
symbol AND1' [H P Q R]
  : Res (H ⟝ ¬ Q ⇒ R) → Res (H ⟝ ¬ P ⇒ R) → Res (H ⟝ ¬ (P ∧ Q) ⇒ R)
≔ λ ρ₁ ρ₂, result (obtain ρ₁ ∧ obtain ρ₂);

// AND2': one antecedent → Schema 1.
symbol AND2' [H P Q]
  : Res (H ⟝ P ⇒ ¬ Q) → Res (H ⟝ ¬ (P ∧ Q))
≔ λ ρ, result (obtain ρ);

// AND3': one antecedent → Schema 1.
symbol AND3' [H P Q R]
  : Res (H ⟝ P ⇒ (Q ⇒ R)) → Res (H ⟝ (P ∧ Q) ⇒ R)
≔ λ ρ, result (obtain ρ);

// AND4': two antecedents → Schema 2.
symbol AND4' [H P Q]
  : Res (H ⟝ Q) → Res (H ⟝ P) → Res (H ⟝ P ∧ Q)
≔ λ ρ₁ ρ₂, result (obtain ρ₁ ∧ obtain ρ₂);

// AND5': Schema 1.
symbol AND5' [H P Q A B R]
  : ⁇ ((P ∧ Q) contient (A ⇒ B))
  → ⁇ (retirer (A ⇒ B) (P ∧ Q) contient A)
  → Res (H ⟝ retirer (A ⇒ B) (P ∧ Q) ∧ B ⇒ R)
  → Res (H ⟝ (P ∧ Q) ⇒ R)
≔ λ _ _ ρ, result (obtain ρ);
