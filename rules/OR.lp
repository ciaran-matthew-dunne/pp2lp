require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------
// 5.2. Disjunction
// ----------------------------------------------

symbol OR1 [H : El (list prd)] [P Q R : El prd] :
  ⟐ (H ⟝ not P => (not Q => R)) →
  ⟐ (H ⟝ not (P or Q) => R);

symbol OR2 [H : El (list prd)] [P Q : El prd] :
  ⟐ (H ⟝ not Q) →
  ⟐ (H ⟝ not P) →
  ⟐ (H ⟝ not (P or Q));

symbol OR3 [H : El (list prd)] [P Q R : El prd] :
  ⟐ (H ⟝ Q => R) →
  ⟐ (H ⟝ P => R) →
  ⟐ (H ⟝ (P or Q) => R);

symbol OR4 [H : El (list prd)] [P Q : El prd] :
  ⟐ (H ⟝ not P => Q) →
  ⟐ (H ⟝ (P or Q));
