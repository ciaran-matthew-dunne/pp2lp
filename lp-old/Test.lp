require open
  pp2lp.Rules pp2lp.Interp;

type AND4;
compute  Π [H : Hyp], Π [P : Prd], Π [Q : Prd], ▷ (H ⟝ Q) → ▷ (H ⟝ P) → ▷ (H ⟝ (P ∧ Q));
