require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------
// 5.3. Implication
// ----------------------------------------------
//
symbol IMP1 [H : El (list prd)] [P Q R : El prd] :
  ⟐ (H ⟝ P => (not Q => R)) →
  ⟐ (H ⟝ not (P => Q) => R);

symbol IMP2 [H : El (list prd)] [P Q : El prd] :
  ⟐ (H ⟝ not Q) →
  ⟐ (H ⟝ P) → // This is "H ⊢ P" in the antecedent
  ⟐ (H ⟝ not (P => Q));

symbol IMP3 [H : El (list prd)] [P Q R : El prd] :
  ⟐ (H ⟝ Q => R) →
  ⟐ (H ⟝ not(P) => R) →
  ⟐ (H ⟝ (P => Q) => R);

symbol IMP4 [H : El (list prd)] [P Q : El prd] :
  ⟐ (P ∷ H ⟝ Q) → ⟐ (H ⟝ P => Q);

symbol IMP5 [H : El (list prd)] [P Q : El prd] :
  Prf (elem P H) → // Side condition: "P est dans H"
  ⟐ (H ⟝ Q) →
  ⟐ (H ⟝ P => Q);

symbol IMP4' [H : El (list prd)] [P Q R S : El prd] : //???
  TYPE;
