require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------
// 5.6. Axioms
// ----------------------------------------------
symbol AXM1 [H : El (list prd)] [P Q : El prd] :
  Prf (elem (not P) H) →
  ⟐ (H ⟝ P => Q);

symbol AXM2 [H : El (list prd)] [P Q : El prd] :
  Prf (elem P H) →
  ⟐ (H ⟝ not P => Q);

symbol AXM3 [H : El (list prd)] [P : El prd] :
  Prf (elem P H) →
  ⟐ (H ⟝ P);

symbol AXM4 [H : El (list prd)] [P R : El prd] :
  Prf (elem R H) →
  ⟐ (H ⟝ P => R);

symbol AXM5 [H : El (list prd)] [P Q R : El prd] :
  Prf (elem (not Q) H) →
  ⟐ (H ⟝ P => (Q => R));

symbol AXM6 [H : El (list prd)] [P Q R : El prd] :
  Prf (elem Q H) →
  ⟐ (H ⟝ P => (not Q => R));

symbol AXM7 [H : El (list prd)] [P : El prd] :
  ⟐ (H ⟝ P => P);

// This rule seems to involve pattern matching and substitution within a conjunction,
// similar to AND5.
symbol AXM8 [H : El (list prd)] [P R : El prd] :
  // Antécédents: "P and · · · contient R"
  // Conséquent: "H ⊢ P and · · · => R"
  // This rule implies some kind of simplification or reduction within a conjunction.
  TYPE;

// This rule involves existential quantification and substitution not directly expressible.
symbol AXM9 [H : El (list prd)] [R Q : El prd] :
  // Antécédents: "forall x · not ( VRAI and P ) est dans H", "On a E tel que [x := E] P = R"
  // Conséquent: "H ⊢ R => Q"
  // This rule appears to be about existential instantiation or a form of it.
  TYPE;
