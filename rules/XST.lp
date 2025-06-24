require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------
// 5.8. Existential quantification
// ----------------------------------------------

symbol XST1 [x y : El idt] [H : El (list prd)] [P R : El prd] :
  Prf (distinct x y) →
  ⟐ (H ⟝ not (∃ (x ⨾ y) P) => R ) →
  ⟐ (H ⟝ not (∃ (? x) (∃ (? y) P)) => R );

symbol XST2 [x y : El idt] [H : El (list prd)] [P : El prd] :
  Prf (distinct x y) →
  ⟐ (H ⟝ not (∃ (x ⨾ y) P) ) →
  ⟐ (H ⟝ not (∃ (? x) (∃ (? y) P)));

symbol XST3 [x y : El idt] [H : El (list prd)] [P R : El prd] :
  Prf (distinct x y) →
  ⟐ (H ⟝ (∃ (x ⨾ y) P) => R ) →
  ⟐ (H ⟝ (∃ (? x) (∃ (? y) P)) => R );

symbol XST4 [x y : El idt] [H : El (list prd)] [P : El prd] :
  Prf (distinct x y) →
  ⟐ (H ⟝ ∃ (x ⨾ y) P) →
  ⟐ (H ⟝ ∃ (? x) (∃ (? y) P));

symbol XST5 [x : El idt] [H : El (list prd)] [P R : El prd] :
  ⟐ (H ⟝ (forall (? x) not P) => R) →
  ⟐ (H ⟝ not (∃ (? x) P) => R);

symbol XST51 [x : El idt] [H : El (list prd)] [P R : El prd] :
  ⟐ (H ⟝ (forall (? x) P) => R) →
  ⟐ (H ⟝ not (∃ (? x) not P) => R);

symbol XST6 [x : El idt] [H : El (list prd)] [P : El prd] :
  ⟐ (H ⟝ forall (? x) not P) →
  ⟐ (H ⟝ not (∃ (? x) P));

symbol XST61 [x : El idt] [H : El (list prd)] [P : El prd] :
  ⟐ (H ⟝ forall (? x) P) →
  ⟐ (H ⟝ not (∃ (? x) not P));

// Similar to ALL5, involves free variables and substitution.
symbol XST7 [x : El idt] [H : El (list prd)] [P R Q : El prd] :
  // First variant: "x non libre dans R"
  // Antécédents: "H ⊢ forall x · ( P => R )"
  // Conséquent: "H ⊢ ( ∃ x · P ) => R"
  TYPE;
  // Second variant: "x est libre dans R", "y n'est libre ni dans P ni dans R", "Q est le résultat de la substitution [x := y] P"
  // Antécédents: "H ⊢ forall y · ( Q => R )"
  // Conséquent: "H ⊢ ( ∃ x · P ) => R"
  // TYPE;

// These rules involve the '⇝' operator and possibly existential discharge.
symbol XST8 [x y : El idt] [H : El (list prd)] [P R A : El prd] :
  // First variant: "x non libre dans H"
  // Antécédents: "( H ⊢ not P ) ⇝ R", "H ⊢ ( forall x · R ) => FAUX"
  // Conséquent: "H ⊢ ∃ x · P"
  TYPE;
  // Second variant: "x est libre dans H", "y n'est libre ni dans A ni dans H", "P est le résultat de la substitution [x := y] A"
  // Antécédents: "( H ⊢ not P ) ⇝ R", "H ⊢ ( forall x · R ) => FAUX"
  // Conséquent: "H ⊢ ( ∃ x · A )"
  // TYPE;
