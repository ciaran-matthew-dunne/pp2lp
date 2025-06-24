require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------
// 5.4. Equivalence
// ----------------------------------------------

symbol EQV1 [H : El (list prd)] [P Q R : El prd] :
  ⟐ (H ⟝ P => (not Q => R)) →
  ⟐ (H ⟝ not P => (Q => R)) →
  ⟐ (H ⟝ not (P <=> Q) => R);

symbol EQV2 [H : El (list prd)] [P Q : El prd] :
  ⟐ (H ⟝ P => not Q) →
  ⟐ (H ⟝ not Q => P) →
  ⟐ (H ⟝ not (P <=> Q));

symbol EQV3 [H : El (list prd)] [P Q R : El prd] :
  ⟐ (H ⟝ P => (Q => R)) →
  ⟐ (H ⟝ not P => (not Q => R)) →
  ⟐ (H ⟝ (P <=> Q) => R);

symbol EQV4 [H : El (list prd)] [P Q : El prd] :
  ⟐ (H ⟝ P => Q) →
  ⟐ (H ⟝ Q => P) →
  ⟐ (H ⟝ (P <=> Q));
