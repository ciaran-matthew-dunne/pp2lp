require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------
// 5.12. Normalization rules
// ----------------------------------------------
symbol NRM1 [H : El (list prd)] [P : El prd] [S : El prd] :
  ⟐ (H ⟝ P => S) →
  ⟐ (H ⟝ (`♢ x, P) => S);

symbol NRM2 [H : El (list prd)] [P Q S : El prd] :
  ⟐ (H ⟝ P => (`♢ x, Q) => S) →
  ⟐ (H ⟝ `♢ x, (P => Q) => S);

symbol NRM3 [H : El (list prd)] [P Q S : El prd] :
  Prf (¬ (Q ≈ FAUX)) →
  ⟐ (H ⟝ (Q => S) and ((`! x, not P) => S)) →
  ⟐ (H ⟝ `♢ x, (P => Q) => S);

symbol NRM4 [H : El (list prd)] [P Q R S : El prd] :
  ⟐ (H ⟝ (Q => `♢ x, (P => R)) => S) →
  ⟐ (H ⟝ `♢ x, (P => (Q => R)) => S);

symbol NRM5 [H : El (list prd)] [P Q R S : El prd] :
  ⟐ (H ⟝ `♢ x, (P and Q => R) => S) →
  ⟐ (H ⟝ `♢ x, (P => (Q => R)) => S);

symbol NRM6 [H : El (list prd)] [P Q R S : El prd] :
  ⟐ (H ⟝ `♢ x, (R => P) => (`♢ x, (R => Q) => S)) →
  ⟐ (H ⟝ `♢ x, (R => P and Q) => S);

symbol NRM7 [H : El (list prd)] [P Q S : El prd] :
  ⟐ (H ⟝ (`♢ x, P) => ((`♢ x, Q) => S)) →
  ⟐ (H ⟝ (`♢ x, (P and Q) => S));

symbol NRM8 [H : El (list prd)] [Q S : El prd] :
  ⟐ (H ⟝ (`♢ x, `♢ y, Q) => S) →
  ⟐ (H ⟝ (`♢ x, `! y, Q) => S);

symbol NRM8_1 : TYPE;

symbol NRM9 [H : El (list prd)] [P Q S : El prd] :
  ⟐ (H ⟝ `♢ x, `♢ y, (P => Q) => S) →
  ⟐ (H ⟝ `♢ x, (P => `! y, Q) => S);

symbol NRM9_1 : TYPE;

symbol NRM10 [H : El (list prd)] [P Q R : El prd] :
  ⟐ (H ⟝ `♡ x, not (P and Q) => R) →
  ⟐ (H ⟝ `♢ x, (P and Q => FAUX) => R);

symbol NRM11 [H : El (list prd)] [P R : El prd] :
  ⟐ (H ⟝ `♡ x, not (VRAI and P) => R) →
  ⟐ (H ⟝ `♢ x, (P => FAUX) => R);

symbol NRM12 [H : El (list prd)] [P Q R : El prd] : TYPE;

symbol NRM13 [H : El (list prd)] [P Q R : El prd] : TYPE;

symbol NRM14 [H : El (list prd)] [P R : El prd] : TYPE;

symbol NRM15 [H : El (list prd)] [P R : El prd] : TYPE;

symbol NRM16 [H : El (list prd)] [P Q : El prd] : TYPE;

symbol NRM17 [H : El (list prd)] [P R Q : El prd] [E : El exp] : TYPE;

symbol NRM18 [H : El (list prd)] [P R Q : El prd] [E : El exp] : TYPE;

symbol NRM19 [H : El (list prd)] [P R Q : El prd] [E : El exp] : TYPE;

symbol NRM20 [H : El (list prd)] [P Q : El prd] [E : El exp] : TYPE;

symbol NRM21 [H : El (list prd)] [P Q : El prd] [E : El exp] : TYPE;

symbol NRM22 [H : El (list prd)] [P Q : El prd] [E : El exp] : TYPE;

symbol NRM23 [H : El (list prd)] [P Q : El prd] [E : El exp] : TYPE;

symbol NRM24 [H : El (list prd)] [P Q : El prd] : TYPE;

symbol NRM25 [H : El (list prd)] [P : El prd] : TYPE;

symbol NRM26 [H : El (list prd)] [P : El prd] : TYPE;

symbol NRM27 [H : El (list prd)] [P Q : El prd] : TYPE;

symbol NRM29 [H : El (list prd)] [P Q S R : El prd] [a b : El exp] : TYPE;

symbol NRM29_1 [H : El (list prd)] [P Q S R : El prd] [a b : El exp] : TYPE;

symbol NRM30 [H : El (list prd)] [P Q S R : El prd] [a b : El exp] : TYPE;

symbol NRM30_1 [H : El (list prd)] [P Q S R : El prd] [a b : El exp] : TYPE;
