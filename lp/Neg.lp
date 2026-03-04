// Negation rules (spec §A.5)
require open pp2lp.B pp2lp.Eq pp2lp.Interp;

// ---- base rules ----------------

opaque symbol NOT1 [H P R]
  : (H ⊩ P ⇒ R) → (H ⊩ ¬ ¬ P ⇒ R) ≔
begin
  assume H P R; simplify; assume one h nnp;
  refine one h (¬¬ₑ _ nnp)
end;

opaque symbol NOT2 [H P]
  : (H ⊩ P) → (H ⊩ ¬ ¬ P) ≔
begin
  assume H P; simplify; assume one h np;
  refine np (one h)
end;

// ---- primed (result-producing) variants ----------------

// NOT1': one antecedent → Schema 1.
symbol NOT1' [H P R]
  : Res (H ⟝ P ⇒ R) → Res (H ⟝ ¬ ¬ P ⇒ R)
≔ λ ρ, result (obtain ρ);

// NOT2': one antecedent → Schema 1.
symbol NOT2' [H P]
  : Res (H ⟝ P) → Res (H ⟝ ¬ ¬ P)
≔ λ ρ, result (obtain ρ);
