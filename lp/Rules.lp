require open
  Logic.U.Set Logic.U.Prop Logic.U.Arrow
  pp2lp.Prelude pp2lp.Syntax;

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


// ----------------------------------------------
// 5.3. Implication
// ----------------------------------------------
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


// ----------------------------------------------
// 5.4. Equivalence
// ----------------------------------------------
symbol EQV1 [H : El (list prd)] [P Q R : El prd] :
  ⟐ (H ⟝ P => (not Q => R)) →
  ⟐ (H ⟝ not P => (Q => R)) →
  ⟐ (H ⟝ not (P <=> Q) => R);

symbol EQV2 [H : El (list prd)] [P Q : El prd] :
  ⟐ (H ⟝ P => not Q) →
  ⟐ (H ⟝ not Q => P) →
  ⟐ (H ⟝ not (P <=> Q));

symbol EQV3 [H : El (list prd)] [P Q R : El prd] :
  ⟐ (H ⟝ P => (Q => R)) →
  ⟐ (H ⟝ not P => (not Q => R)) →
  ⟐ (H ⟝ (P <=> Q) => R);

symbol EQV4 [H : El (list prd)] [P Q : El prd] :
  ⟐ (H ⟝ P => Q) →
  ⟐ (H ⟝ Q => P) →
  ⟐ (H ⟝ (P <=> Q));


// ----------------------------------------------
// 5.5. Negation
// ----------------------------------------------
symbol NOT1 [H : El (list prd)] [P R : El prd] :
  ⟐ (H ⟝ P => R) →
  ⟐ (H ⟝ not not P => R);

symbol NOT2 [H : El (list prd)] [P : El prd] :
  ⟐ (H ⟝ P) →
  ⟐ (H ⟝ not not P);

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

symbol AXM8 [H : El (list prd)] [P R : El prd] :
  TYPE;

symbol AXM9 [H : El (list prd)] [R Q : El prd] :
  TYPE;


// ----------------------------------------------
// 5.7. Universal quantification
// ----------------------------------------------
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

// ----------------------------------------------
// 5.9. Vrai et Faux
// ----------------------------------------------
symbol VR1 [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ not VRAI => R);

symbol VR2 [H : El (list prd)] :
  ⟐ (H ⟝ VRAI) →
  ⟐ (H ⟝ not VRAI);

symbol VR3 [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ R) →
  ⟐ (H ⟝ VRAI => R);

symbol VR4 [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ VRAI);

symbol FX1 [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ R) →
  ⟐ (H ⟝ not VRAI => R);

symbol FX2 [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ not VRAI);

symbol FX3 [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ VRAI => R);


// ----------------------------------------------
// 5.10. STOP rules
// ----------------------------------------------
symbol STOP [H : El (list prd)] [P : El prd] :
  Prf (¬ (P ≈ FAUX)) →
  ⟐ (H ⟝ not P => FAUX) →
  ⟐ (H ⟝ P);

symbol STOP' [H : El (list prd)] [P : El prd] :
  Prf ((H ⟝ P) ⟿ P);

// ----------------------------------------------
// 5.11 INS rule
// ----------------------------------------------
symbol INS [H Q : El (list prd)] :
  ⟐ (H ⟝ Q ⭆ FAUX) →
  ⟐ (H ⟝ FAUX);

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

symbol NRM12 [H : El (list prd)] [P Q R : El prd] :
  ⟐ (H ⟝ `♡ x, not (P and Q) => R) →
  ⟐ (H ⟝ `♢ x, (P => not Q) => R);

symbol NRM13 [H : El (list prd)] [P Q R : El prd] :
  ⟐ (H ⟝ `♡ x, not (P and not Q) => R) →
  ⟐ (H ⟝ `♢ x, (P => Q) => R);

symbol NRM14 [H : El (list prd)] [P R : El prd] :
  ⟐ (H ⟝ `♡ x, not (VRAI and P) => R) →
  ⟐ (H ⟝ (`♢ x, not P) => R);

symbol NRM15 [H : El (list prd)] [P R : El prd] :
  ⟐ (H ⟝ `♡ x, not (VRAI and not P) => R) →
  ⟐ (H ⟝ (`♢ x, P) => R);

symbol NRM16 [H : El (list prd)] [P : El (exp ⤳ prd)] [Q : El prd] :
  Prf (elem (! P) H) →
  ⟐ (H ⟝ Q) →
  ⟐ (H ⟝ (♡ P) => Q);

// hopefully higher-order unification sorts this out
symbol NRM17 [H : El (list prd)] [P : El (exp ⤳ prd)] [Q : El prd] [E : El exp] :
  Prf (elem (`! x, not (VRAI and P x)) H) →
  ⟐ (H ⟝ (`♡ y, not (VRAI and not (P E))) => Q);

symbol NRM18 [H : El (list prd)] [P : El (exp ⤳ prd)] [R Q : El prd] [E : El exp] :
  Prf (elem (`! x, not (VRAI and not (P x))) H) →
  Prf (P E ≈ R) →
  ⟐ (H ⟝ (`♡ y, not (VRAI and R)) => Q);

symbol NRM19 [H : El (list prd)] [R : El (exp ⤳ prd)] [P Q : El prd] [E : El exp] :
  Prf (elem P H) →
  Prf ((R E) ≈ P) →
  ⟐ (H ⟝ (`♡ x, not (VRAI and (R x))) => Q);

symbol NRM20 [H : El (list prd)] [P : El (exp ⤳ prd)] [Q : El prd] [E : El exp] :
  ⟐ (H ⟝ `♡ y, not (P E) => Q) →
  ⟐ (H ⟝ `♡ x, `♡ y, not (P x and (E = x)) => Q);

symbol NRM21 [H : El (list prd)] [P : El (exp ⤳ prd)] [Q : El prd] [E : El exp] :
  ⟐ (H ⟝ `♡ y, not (P E) => Q) →
  ⟐ (H ⟝ `♡ x, `♡ y, not (P x and (x = E)) => Q);

symbol NRM22 [H : El (list prd)] [P : El (exp ⤳ prd)] [Q : El prd] [E : El exp] :
  ⟐ (H ⟝ not (P E) => Q) →
  ⟐ (H ⟝ `♡ x, not (P x and (x = E)) => Q);

symbol NRM23 [H : El (list prd)] [P : El (exp ⤳ prd)] [Q : El prd] [E : El exp] :
  ⟐ (H ⟝ not (P E) => Q) →
  ⟐ (H ⟝ `♡ x, not (P x and (E = x)) => Q);

sequential symbol NRM24_aux : El (prd ⤳ bool);
rule NRM24_aux ($A and $B) ↪ ⊥
with NRM24_aux  _          ↪ ⊥ ;

symbol NRM24 [H : El (list prd)] [P Q : El prd] :
  Prf (NRM24_aux P) →
  ⟐ (H ⟝ `♡ x, not (VRAI and P) => Q) →
  ⟐ (H ⟝ `♡ x, not P => Q);

symbol NRM25 [H : El (list prd)] [P : El prd] :
  ⟐ (H ⟝ P) →
  ⟐ (H ⟝ `♡ x, P);

symbol NRM26 [H : El (list prd)] [P : El (exp ⤳ prd)] :
  ⟐ (H ⟝ `♡ x, P x) →
  ⟐ (H ⟝ `♡ x, `♡ y, P x);

// ---- stuff for arithmetic ??? -------
symbol NRM27 [H : El (list prd)] [P Q : El prd] : TYPE;

symbol NRM29 [H : El (list prd)] [P Q S R : El prd] [a b : El exp] : TYPE;

symbol NRM29_1 [H : El (list prd)] [P Q S R : El prd] [a b : El exp] : TYPE;

symbol NRM30 [H : El (list prd)] [P Q S R : El prd] [a b : El exp] : TYPE;

symbol NRM30_1 [H : El (list prd)] [P Q S R : El prd] [a b : El exp] : TYPE;

// ----------------------------------------------
// 5.13. Rules for equality
// ----------------------------------------------

symbol EVR1 [H : El (list prd)] [P : El prd] [E : El exp] :
  ⟐ (H ⟝ not (E = E) => P);

// BROKEN. need 'builtin' integration
symbol EVR11 [H : El (list prd)] [P : El prd] [n m : El exp] :
  Prf (¬ (n ≈ m)) →
  ⟐ (H ⟝ (n = m) => P) →
  TYPE;

symbol EVR2 [H : El (list prd)] [E : El exp] :
  ⟐ (H ⟝ FAUX) →
  ⟐ (H ⟝ not (E = E));

symbol EVR3 [H : El (list prd)] [P : El prd] [E : El exp] :
  ⟐ (H ⟝ P) →
  ⟐ (H ⟝ (E = E) => P);

symbol EVR4 [H : El (list prd)] [E : El exp] :
  ⟐ (H ⟝ (E = E));

symbol EAXM1 [H : El (list prd)] [E F : El exp] [P : El prd] :
  Prf (elem (not (F = E)) H) →
  ⟐ (H ⟝ (E = F) => P);

symbol EAXM2 [H : El (list prd)] [E F : El exp] [P : El prd] :
  Prf (elem (F = E) H) →
  ⟐ (H ⟝ not (E = F) => P);

symbol EAXM3_1 [H : El (list prd)] [E F : El exp] [P : El prd] :
  Prf (elem (F = E) H) →
  ⟐ (H ⟝ (E = F));

symbol EAXM3_2 [H : El (list prd)] [E F : El exp] [P : El prd] :
  Prf (elem (not (F = E)) H) →
  ⟐ (H ⟝ not (E = F));

symbol EIMP5_1 [H : El (list prd)] [E F : El exp] [P : El prd] :
  Prf (elem (not (F = E)) H) →
  ⟐ (H ⟝ P) →
  ⟐ (H ⟝ not (E = F) => P);

symbol EIMP5_2 [H : El (list prd)] [E F : El exp] [P : El prd] :
  Prf (elem (F = E) H) →
  ⟐ (H ⟝ P) →
  ⟐ (H ⟝ (E = F) => P);

symbol EQC1 [H : El (list prd)] [a b c d : El exp] [P : El prd] :
  ⟐ (H ⟝ not (a = c) or not (b = d) => P) →
  ⟐ (H ⟝ not (opair a b = opair c d) => P);

symbol EQC2 [H : El (list prd)] [a b c d : El exp] [P : El prd] :
  ⟐ (H ⟝ (a = c) and (b = d) => P) →
  ⟐ (H ⟝  (opair a b = opair c d) => P);

symbol EQS1 [H : El (list prd)] [E F : El exp] [P : El prd] :
  ⟐ (H ⟝ (E = F) => P) →
  ⟐ (H ⟝ (eql_set E F) => P);

symbol EQS2 [H : El (list prd)] [E F : El exp] [P : El prd] :
  ⟐ (H ⟝ FAUX => P) →
  ⟐ (H ⟝ not (eql_set E F) => P);

symbol EAXM9_1 [H : El (list prd)] [p q : El (exp ⤳ exp)] [E : El exp] [Q : El prd] :
  Prf (elem (`! x, not (VRAI and (p x = q x))) H) →
  ⟐ (H ⟝ ((p E) = (q E)) => Q);

symbol EAXM9_2 [H : El (list prd)] [p q : El (exp ⤳ exp)] [E : El exp] [Q : El prd] :
  Prf (elem (`! x, not (VRAI and not (p x = q x))) H) →
  ⟐ (H ⟝ not ((p E) = (q E)) => Q);

symbol OPR1 [H : El (list prd)] [P : El (exp ⤳ prd)] [x E : El exp] :
  ⟐ (H ⟝ P E) →
  ⟐ (H ⟝ (x = E) => P x);

symbol OPR2 [H : El (list prd)] [P : El (exp ⤳ prd)] [x E : El exp] :
  ⟐ (H ⟝ P E) →
  ⟐ (H ⟝ (E = x) => P x);

symbol ECTR1 [H : El (list prd)] [P : El prd] [Q : El (exp ⤳ prd)] [E F : El exp] :
  Prf (elem (not (Q E)) H) →
  Prf (elem (Q F) H) →
  ⟐ (H ⟝ (E = F) => P);

symbol ECTR2 [H : El (list prd)] [P : El prd] [Q : El (exp ⤳ prd)] [E F : El exp] :
  Prf (elem (not (Q E)) H) →
  Prf (elem (Q F) H) →
  ⟐ (H ⟝ (F = E) => P);

symbol ECTR3 [H : El (list prd)] [Q : El prd] [P : El (exp ⤳ prd)] [E F : El exp] :
  Prf (elem (E = F) H) →
  Prf (elem (P F) H) →
  ⟐ (H ⟝ not (P E) => Q);

symbol ECTR4 [H : El (list prd)] [Q : El prd] [P : El (exp ⤳ prd)] [E F : El exp] :
  Prf (elem (F = E) H) →
  Prf (elem (P F) H) →
  ⟐ (H ⟝ not (P E) => Q);

symbol ECTR5 [H : El (list prd)] [Q : El prd] [P : El (exp ⤳ prd)] [E F : El exp] :
  Prf (elem (E = F) H) →
  Prf (elem (not (P F)) H) →
  ⟐ (H ⟝ P E => Q);

symbol ECTR6 [H : El (list prd)] [Q : El prd] [P : El (exp ⤳ prd)] [E F : El exp] :
  Prf (elem (F = E) H) →
  Prf (elem (not (P F)) H) →
  ⟐ (H ⟝ P E => Q);

// ----------------------------------------------
// 5.14. Règles sur l'arithmétique (Arithmetic Rules)
// ----------------------------------------------

symbol AR1 [H : El (list prd)] [E : El exp] [R : El prd] :
  ⟐ (H ⟝ R) →
  ⟐ (H ⟝ (E ≤ E) => R);

symbol AR2 [a b : El exp] [H : El (list prd)] [R : El prd] :
  TYPE;

symbol AR3 [a : El exp] [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ ((𝟏 - a) ≤ 𝟎) => R) →
  ⟐ (H ⟝ not (a ≤ 𝟎) => R);

symbol AR4 [E F : El exp] [H : El (list prd)] [R : El prd] :
  TYPE;

symbol AR5 [a : El exp] [H : El (list prd)] [R : El prd] :
  TYPE;

symbol AR6 [a : El exp] [H : El (list prd)] [R : El prd] :
  TYPE;

symbol AR7 [a b c : El exp] [H : El (list prd)] [R : El prd] :
  TYPE;

symbol AR8 [a b c : El exp] [H : El (list prd)] [R : El prd] :
  TYPE;

symbol AR9 [E F : El exp] [H : El (list prd)] [R : El prd] :
  TYPE;

symbol AR10 [H : El (list prd)] [P R : El prd] :
  ⟐ (H ⟝ (solveur P) => R) →
  ⟐ (H ⟝ P => R);

symbol AR11 [x : El exp] [H : El (list prd)] [P : El prd] :
  ⟐ (H ⟝ not (x ≤ x) => P);

symbol AR12 [a b : El exp] [H : El (list prd)] [P : El prd] : TYPE;

// ----------------------------------------------
// 5.15 Booleans
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
