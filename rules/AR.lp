require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------
// 5.14. Règles sur l'arithmétique (Arithmetic Rules)
// ----------------------------------------------

symbol AR1 [H : El (list prd)] [E : El exp] [R : El prd] :
  ⟐ (H ⟝ R) →
  ⟐ (H ⟝ (E ≤ E) => R);

symbol AR2 [a b : El exp] [H : El (list prd)] [R : El prd] :
  // Side conditions: "a est numérique", "b est numérique", "a > b"
  TYPE; // Stub due to numeric specific conditions.

symbol AR3 [a : El exp] [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ ((𝟏 - a) ≤ 𝟎) => R) →
  ⟐ (H ⟝ not (a ≤ 𝟎) => R);

symbol AR4 [E F : El exp] [H : El (list prd)] [R : El prd] :
  // Side conditions: "F ≤ 0 est dans H", "E + F > 0"
  TYPE; // Stub due to side conditions.

// These rules involve '≪' which likely means strictly less than.
symbol AR5 [a : El exp] [H : El (list prd)] [R : El prd] :
  // Side condition: "a ≪ 0 est dans H" (a < 0 is in H)
  TYPE; // Stub.

symbol AR6 [a : El exp] [H : El (list prd)] [R : El prd] :
  // Side condition: "−a ≪ 0 est dans H" (-a < 0 is in H)
  TYPE; // Stub.

symbol AR7 [a b c : El exp] [H : El (list prd)] [R : El prd] :
  // Side conditions: "c + b ≪ 0 est dans H", "a + c = 0"
  TYPE; // Stub.

symbol AR8 [a b c : El exp] [H : El (list prd)] [R : El prd] :
  // Side conditions: "a − b ≪ 0 est dans H", "a + c = 0"
  TYPE; // Stub.

symbol AR9 [E F : El exp] [H : El (list prd)] [R : El prd] :
  // Side condition: "solveur(E) = F"
  TYPE; // Stub for external solver.

symbol AR10 [H : El (list prd)] [P R : El prd] :
  ⟐ (H ⟝ (solveur P) => R) →
  ⟐ (H ⟝ P => R);

symbol AR11 [x : El exp] [H : El (list prd)] [P : El prd] :
  ⟐ (H ⟝ not (x ≤ x) => P);

symbol AR12 [a b : El exp] [H : El (list prd)] [P : El prd] : TYPE;
  //⟐ ((a ≤ b) ∷ H ⟝ P) → // H,(a ≤ b) ⊢ P
  //⟐ (H ⟝ ((a ≪ b) => P)); // Assuming ≪ means strictly less than.
