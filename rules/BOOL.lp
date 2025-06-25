require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------
// 5.8. Booleans
// ----------------------------------------------
// in contrast to `VRAI` and `FAUX` in `VRFX` (both of type `prd`),
// the rules in this file operate on boolean values of type `exp`.
symbol FALSE : El exp;
symbol TRUE : El exp;

symbol BOOL1_1 [H : El (list prd)] [P : El prd] [v : El exp] :
  ⟐ ((not (v = FALSE)) ∷ (v = TRUE) ∷ H ⟝ P) →
  ⟐ (H ⟝ (v = TRUE) => P);

symbol BOOL1_2 [H : El (list prd)] [P : El prd] [v : El exp] :
  ⟐ ((v = FALSE) ∷ (not (v = TRUE)) ∷ H ⟝ P) →
  ⟐ (H ⟝ (v = FALSE) => P);

symbol BOOL2_1 [H : El (list prd)] [P : El prd] [v : El exp] :
  ⟐ (H ⟝ (v = TRUE) => P) →
  ⟐ (H ⟝ (TRUE = v) => P);

symbol BOOL2_2 [H : El (list prd)] [P : El prd] [v : El exp] :
  ⟐ (H ⟝ (v = FALSE) => P) →
  ⟐ (H ⟝ (FALSE = v) => P);

symbol BOOL3_1 [H : El (list prd)] [P : El prd] [v : El exp] :
  ⟐ (H ⟝ (v = FALSE) => P) →
  ⟐ (H ⟝ not (v = TRUE) => P);

symbol BOOL3_2 [H : El (list prd)] [P : El prd] [v : El exp] :
  ⟐ (H ⟝ (v = TRUE) => P) →
  ⟐ (H ⟝ not (v = FALSE) => P);

symbol BOOL4_1 [H : El (list prd)] [P : El prd] [v : El exp] :
  ⟐ (H ⟝ (v = FALSE) => P) →
  ⟐ (H ⟝ not (TRUE = v) => P);

symbol BOOL4_2 [H : El (list prd)] [P : El prd] [v : El exp] :
  ⟐ (H ⟝ (v = TRUE) => P) →
  ⟐ (H ⟝ not (FALSE = v) => P);

symbol BOOL5_1 [H : El (list prd)] [P : El prd] [v : El exp] :
  ⟐ (H ⟝ (TRUE = FALSE) => P);

symbol BOOL5_2 [H : El (list prd)] [P : El prd] [v : El exp] :
  ⟐ (H ⟝ (FALSE = TRUE) => P);
