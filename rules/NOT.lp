require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------
// 5.5. Negation
// ----------------------------------------------
symbol NOT1 [H : El (list prd)] [P R : El prd] :
  ⟐ (H ⟝ P => R) →
  ⟐ (H ⟝ not not P => R);

symbol NOT2 [H : El (list prd)] [P : El prd] : // R is not present in the Conséquent of NOT2
  ⟐ (H ⟝ P) →
  ⟐ (H ⟝ not not P); // The source defines H ⊢ notnotP, not H ⊢ notnotP => R.
