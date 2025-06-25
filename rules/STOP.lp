require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------
// 5.10. STOP rules
// ----------------------------------------------
symbol STOP [H : El (list prd)] [P : El prd] :
  Prf (¬ (P ≈ FAUX)) →
  ⟐ (H ⟝ not P => FAUX) →
  ⟐ (H ⟝ P);

symbol STOP' [H : El (list prd)] [P : El prd] :
  Prf ((H ⟝ P) ⟿ P);
