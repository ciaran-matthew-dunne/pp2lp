require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------
// 5.8. Vrai et Faux
// ----------------------------------------------

symbol VR1 [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ not VRAI => R);

symbol VR2 [H : El (list prd)] :
  ⟐ (H ⟝ VRAI) →
  ⟐ (H ⟝ not VRAI);

symbol VR3 [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ R) →
  ⟐ (H ⟝ VRAI => R);

symbol VR4 [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ VRAI);

symbol FX1 [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ R) →
  ⟐ (H ⟝ not VRAI => R);

symbol FX2 [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ not VRAI);

symbol FX3 [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ VRAI => R);
