require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------############
// 5.7. Universal quantification
// ----------------------------------------------############
symbol ALL1 [H : El (list prd)] [P R : El prd] :
  ⟐ (H ⟝ (not (`! x, `! y, P)) => R) →
  ⟐ (H ⟝ (not (`! x, `! y, P)) => R);

symbol ALL2 [H : El (list prd)] [P : El prd] :
  ⟐ (H ⟝ not (`! x, `! y, P)) →
  ⟐ (H ⟝ not (`! x, `! y, P));

symbol ALL3 [H : El (list prd)] [P R : El prd] :
  ⟐ (H ⟝ (`! x, `! y, P) => R) →
  ⟐ (H ⟝ (`! x, `! y, P) => R);

symbol ALL4 [x y : El idt] [H : El (list prd)] [P : El prd] :
  ⟐ (H ⟝ `! x, `! y, P) →
  ⟐ (H ⟝ `! x, `! y, P);

symbol ALL5 [H : El (list prd)] [P R : El prd] :
  ⟐ (H ⟝ `! x, (not P => R)) →
  ⟐ (H ⟝ not (`! x, P) => R);

// redundant (??) same as ALL5, but also performs alpha-conversion.
symbol ALL5_1 [H : El (list prd)] [P R : El prd] : TYPE;

symbol ALL6 [H : El (list prd)] [P : El prd] :
  ⟐ (H ⟝ (`! x, P) => VRAI) →
  ⟐ (H ⟝ not (`! x, P));

symbol ALL7 [H : El (list prd)] [P Q R : El prd] :
  Prf ((H ⟝ P) ⟿ R) →
  ⟐ (H ⟝ (`♢ x, R) => Q) →
  ⟐ (H ⟝ (`! x, P) => Q);

// redundant (??) same as ALL7, but also performs alpha-conversion.
symbol ALL7_1 [H : El (list prd)] [P Q R S A : El prd] : TYPE;

symbol ALL7' [H : El (list prd)] [P Q R S : El prd] :
  Prf ((H ⟝ P) ⟿ R) →
  Prf ((H ⟝ (`♢ x, R) => Q) ⟿ S) →
  Prf ((H ⟝ (`! x, P) => Q) ⟿ S);

// redundant (??) same as ALL8', but also performs alpha-conversion.
symbol ALL7'_1 [H : El (list prd)] [P Q R S A : El prd] : TYPE;

symbol ALL8' [H : El (list prd)] [P Q : El prd] :
  Prf ((H ⟝ P) ⟿ Q) →
  Prf ((H ⟝ (`! x, P)) ⟿ (`! x, Q));

// redundant (??) same as ALL8', but also performs alpha-conversion.
symbol ALL8'_1 [H : El (list prd)] [P Q : El prd] : TYPE;

symbol ALL9' [H : El (list prd)] [P : El (exp ⤳ prd)] [Q R : El prd] :
  Prf (((! P) ∷ H ⟝ Q) ⟿ R) →
  Prf ((H ⟝ (♡ P) => Q) ⟿ (! P) => R);
