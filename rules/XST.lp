require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------
// 5.8. Existential quantification
// ----------------------------------------------

symbol XST1 [x y : El idt] [H : El (list prd)] [P R : El prd] :
  ⟐ (H ⟝ not (`# x, `# y, P) => R) →
  ⟐ (H ⟝ not (`# x, `# y, P) => R);

symbol XST2 [x y : El idt] [H : El (list prd)] [P : El prd] :
  ⟐ (H ⟝ not (`# x, `# y, P) ) →
  ⟐ (H ⟝ not (`# x, `# y, P));

symbol XST3 [x y : El idt] [H : El (list prd)] [P R : El prd] :
  ⟐ (H ⟝ (`# x, `# y, P) => R ) →
  ⟐ (H ⟝ (`# x, `# y, P) => R );

symbol XST4 [x y : El idt] [H : El (list prd)] [P : El prd] :
  ⟐ (H ⟝ `# x, `# y, P) →
  ⟐ (H ⟝ `# x, `# y, P);

symbol XST5 [x : El idt] [H : El (list prd)] [P R : El prd] :
  ⟐ (H ⟝ (`! x, not P) => R) →
  ⟐ (H ⟝ not (`# x, P) => R);

symbol XST5_1 [x : El idt] [H : El (list prd)] [P R : El prd] :
  ⟐ (H ⟝ (`! x, P) => R) →
  ⟐ (H ⟝ not (`# x, not P) => R);

symbol XST6 [x : El idt] [H : El (list prd)] [P : El prd] :
  ⟐ (H ⟝ `! x, not P) →
  ⟐ (H ⟝ not (`# x, P));

symbol XST6_1 [x : El idt] [H : El (list prd)] [P : El prd] :
  ⟐ (H ⟝ `! x, P) →
  ⟐ (H ⟝ not (`# x, not P));

symbol XST7 [x : El idt] [H : El (list prd)] [P R Q : El prd] :
  ⟐ (H ⟝ `! x, (P => R)) →
  ⟐ (H ⟝ (`# x, P) => R);

// redunant rule.
symbol XST7_1 [x : El idt] [H : El (list prd)] [P R Q : El prd] : TYPE;

symbol XST8 [x y : El idt] [H : El (list prd)] [P R A : El prd] :
  Prf ((H ⟝ not P) ⟿ R) →
  ⟐ (H ⟝ (`! x, R) => VRAI) →
  ⟐ (H ⟝ (`# x, P));

symbol XST8_1 [x y : El idt] [H : El (list prd)] [P R A : El prd] : TYPE;
