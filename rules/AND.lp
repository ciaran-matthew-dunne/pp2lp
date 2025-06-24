require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------
// 5.1. Conjunction
// ----------------------------------------------

symbol AND1 [H : El (list prd)] [P Q R : El prd] :
  ⟐ (H ⟝ not Q => R) →
  ⟐ (H ⟝ not P => R) →
  ⟐ (H ⟝ not (P and Q) => R);

symbol AND2 [H : El (list prd)] [P Q : El prd] :
  ⟐ (H ⟝ P => not Q) →
  ⟐ (H ⟝ not (P and Q));

symbol AND3 [H : El (list prd)] [P Q R : El prd] :
  ⟐ (H ⟝ P => (Q => R)) →
  ⟐ (H ⟝ (P and Q) => R);

symbol AND4 [H : El (list prd)] [P Q : El prd] :
  ⟐ (H ⟝ Q) →
  ⟐ (H ⟝ P) →
  ⟐ (H ⟝ (P and Q));

symbol AND5 [H : El (list prd)] [P Q R A B : El prd] :
  TYPE;
