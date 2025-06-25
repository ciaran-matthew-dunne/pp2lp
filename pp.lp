require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------
// 5.9. Vrai et Faux (VRAI and VRAI)
// ----------------------------------------------
symbol VR1 [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ not VRAI => R);

symbol VR2 [H : El (list prd)] :
  ⟐ (H ⟝ VRAI) →
  ⟐ (H ⟝ not VRAI);

symbol VR3 [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ R) →
  ⟐ (H ⟝ VRAI => R);

symbol VR4 [H : El (list prd)] :
  ⟐ (H ⟝ VRAI);

symbol FX1 [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ R) →
  ⟐ (H ⟝ not VRAI => R);

symbol FX2 [H : El (list prd)] :
  ⟐ (H ⟝ not VRAI);

symbol FX3 [H : El (list prd)] [R : El prd] :
  ⟐ (H ⟝ VRAI => R);

// ----------------------------------------------
// 5.10. Règles STOP
// ----------------------------------------------
symbol STOP [H : El (list prd)] [P : El prd] :
  // Side condition: "P n'est pas le prédicat FAUX"
  ⟐ (H ⟝ not P => VRAI) →
  ⟐ (H ⟝ P);

// This rule has a 'Résultat' column.
symbol STOP_prime [H : El (list prd)] [P : El prd] :
  // Antécédents: "H ⊢ P"
  // Conséquent: "P" (This consequent format is unusual for sequents, suggesting P itself is the result of applying the rule)
  // Résultat: "P"
  TYPE;

// ----------------------------------------------
// 5.11. Règle INS (Instantiation)
// ----------------------------------------------
symbol INS [H : El (list prd)] [Q1 Q2 Qn : El prd] : // Q1, Q2, ..., Qn are determined by "Détermination des instanciations"
  // Side condition: "Détermination des instanciations Q1, Q2, . . ., Qn"
  // This implies some form of meta-level computation or an external instantiation mechanism.
  //⟐ (H ⟝ Q1 => (Q2 => ... => (Qn => VRAI) ...)) →
  //⟐ (H ⟝ VRAI);
  TYPE;
// ----------------------------------------------
// 5.12. Normalisation
// ----------------------------------------------
// These rules heavily rely on "non libre dans" (not free in), substitution,
// and the '♢' operator (which likely corresponds to 'exists' or a specific type of 'forall2' from the ASCII table).
// Given the complexity of free variable checking, substitution, and the '♢' symbol (which is represented as 'forall2' in the ASCII table but sometimes used for existential quantifiers by convention or specific systems),
// these rules will be stubs.

symbol NRM1 [x : El idt] [H : El (list prd)] [P S : El prd] :
  // Side condition: "x non libre dans P"
  ⟐ (H ⟝ P => S) →
  ⟐ (H ⟝ (forall (? x) P) => S); // Assuming ♢ x is forall x based on the ASCII table
  // However, the NRM rules seem to be about pushing quantifiers through implications,
  // where '♢' often refers to existential (e.g., 'exists x') or a general 'forall' form that can be re-arranged.
  // I will use 'forall' for '♢' based on the ASCII table provided.
  // The '♢' symbol is shown as 'forall2' in the ASCII table, which maps to 'forall'.
  // However, the behavior of some NRM rules, especially with conjunctions (NRM7),
  // suggests '♢' might act like an existential quantifier in certain contexts (distributing over conjunctions).
  // For consistency with the provided table, I'll use forall here.
  // If '♢' means something else (like existential quantification '∃'), the symbol definition for it needs to be explicit.
  //TYPE; // Stub due to 'non libre dans' side condition.

symbol NRM2 [x : El idt] [H : El (list prd)] [P Q S : El prd] :
  // Side condition: "x non libre dans P"
  TYPE; // Stub due to side condition and '♢' interpretation.

symbol NRM3 [x : El idt] [H : El (list prd)] [P Q S : El prd] :
  // Side conditions: "x non libre dans Q", "Q n'est pas le prédicat FAUX"
  TYPE; // Stub due to side conditions and complex antecedent structure.

symbol NRM4 [x : El idt] [H : El (list prd)] [P Q R S : El prd] :
  // Side condition: "x non libre dans Q"
  TYPE; // Stub due to side condition and nested implication with '♢'.

symbol NRM5 [x : El idt] [H : El (list prd)] [P Q R S : El prd] :
  TYPE; // Stub due to '♢' interpretation and complex conjunction/implication.

symbol NRM6 [x : El idt] [H : El (list prd)] [P Q R S : El prd] :
  TYPE; // Stub due to '♢' interpretation and complex antecedent structure.

symbol NRM7 [x : El idt] [H : El (list prd)] [P Q S : El prd] :
  TYPE; // Stub due to '♢' interpretation and nested conjunction/implication.

symbol NRM8 [x y : El idt] [H : El (list prd)] [Q S K : El prd] :
  // First variant: "x et y sont distincts"
  TYPE; // Stub due to '♢' interpretation and nested quantifiers.
  // Second variant: "x et y ne sont pas distinctes", "z est distincte de x et de y", "K est le résultat de la substitution [y := z] Q"
  // TYPE; // Stub.

symbol NRM9 [x y : El idt] [H : El (list prd)] [P Q S K : El prd] :
  // First variant: "x et y sont distincts", "y non libre dans P"
  TYPE; // Stub due to side conditions and '♢' interpretation.
  // Second variant: "x et y ne sont pas distinctes ou y est libre dans P", "z est distincte de x et non libre dans P et dans Q", "K est le résultat de la substitution [y := z] Q"
  // TYPE; // Stub.

symbol NRM10 [x : El idt] [H : El (list prd)] [P Q R : El prd] :
  TYPE; // Stub due to '♢' interpretation.

symbol NRM11 [x : El idt] [H : El (list prd)] [P R : El prd] :
  TYPE; // Stub due to '♢' interpretation and VRAI (VRAI).

symbol NRM12 [x : El idt] [H : El (list prd)] [P Q R : El prd] :
  TYPE; // Stub due to '♢' interpretation.

symbol NRM13 [x : El idt] [H : El (list prd)] [P Q R : El prd] :
  TYPE; // Stub due to '♢' interpretation.

symbol NRM14 [x : El idt] [H : El (list prd)] [P R : El prd] :
  TYPE; // Stub due to '♢' interpretation and VRAI.

symbol NRM15 [x : El idt] [H : El (list prd)] [P R : El prd] :
  TYPE; // Stub due to '♢' interpretation and VRAI.

symbol NRM16 [x : El idt] [H : El (list prd)] [P Q : El prd] :
  Prf (elem (forall (? x) P) H) → // "forall x · P est dans H"
  ⟐ (H ⟝ (forall (? x) P) => Q);

// These rules involve existential instantiation and substitution, which are not directly supported.
symbol NRM17 [x y : El idt] [H : El (list prd)] [P Q R E : El prd] :
  // Side conditions: "forall x · not ( VRAI and P ) est dans H", "On a E tel que [x := E] P = R"
  TYPE; // Stub.

symbol NRM18 [x y : El idt] [H : El (list prd)] [P Q R E : El prd] :
  // Side conditions: "forall x · not ( VRAI and not P ) est dans H", "On a E tel que [x := E] (P) = R"
  TYPE; // Stub.

symbol NRM19 [x : El idt] [H : El (list prd)] [P Q R E : El prd] :
  // Side conditions: "P est dans H", "On a E tel que [x := E] R = P"
  TYPE; // Stub.

// These rules involve 'non libre dans' and substitution, similar to ALL5, XST7, etc.
symbol NRM20 [x y : El idt] [H : El (list prd)] [P Q E : El prd] :
  // Side conditions: "x non libre dans E"
  TYPE; // Stub.

symbol NRM21 [x y : El idt] [H : El (list prd)] [P Q E : El prd] :
  // Side conditions: "x non libre dans E"
  TYPE; // Stub.

symbol NRM22 [x : El idt] [H : El (list prd)] [P Q E : El prd] :
  // Side conditions: "x non libre dans E"
  TYPE; // Stub.

symbol NRM23 [x : El idt] [H : El (list prd)] [P Q E : El prd] :
  // Side conditions: "x non libre dans E"
  TYPE; // Stub.

symbol NRM24 [x : El idt] [H : El (list prd)] [P Q : El prd] :
  // Side condition: "P n'est pas de la forme A and B"
  TYPE; // Stub.

symbol NRM25 [x : El idt] [H : El (list prd)] [P : El prd] :
  // Side condition: "x non libre dans P"
  ⟐ (H ⟝ P) →
  ⟐ (H ⟝ forall (? x) P); // Forall2 (x) corresponds to forall x
  // Assuming 'forall2' is also syntactic sugar for universal quantification.

symbol NRM26 [x y : El idt] [H : El (list prd)] [P : El prd] :
  // Side condition: "y non libre dans P"
  ⟐ (H ⟝ forall (x ∷ nil) P) → // forall2 (x, . . .) · P
  ⟐ (H ⟝ forall (x ∷ y ∷ nil) P); // forall2 (x, y, . . .) · P
  // This rule appears to be for adding universally quantified variables that are not free in P.
  //TYPE; // Stub for more general list of variables.

// These normalization rules involve arithmetic inequalities, variable replacement,
// and a "solver" function, which are beyond the scope of current primitives.
symbol NRM27 [x1 xi xn : El idt] [H : El (list prd)] [P Q R : El prd] :
  // Side conditions: "(xi ≤ 0) est dans (P and . . . and Q)", " (−xi ≤ 0) est dans (P and . . . and Q)", "On a R tel que [xi := 0](P and . . . and Q) = R"
  TYPE; // Stub.

symbol NRM28 [x : El idt] [H : El (list prd)] [P Q R S : El prd] :
  // Side conditions: "(x ≤ 0) est dans (P and . . . and Q)", " (−x ≤ 0) est dans (P and . . . and Q)", "On a S tel que [x := 0](P and . . . and Q) = S"
  TYPE; // Stub.

symbol NRM29 [a b xi : El exp] [x1 xi_minus_1 xi_plus_1 xn : El idt] [H : El (list prd)] [P Q R S : El prd] :
  // Side conditions: "(a + xi ≤ 0) est dans (P and . . . and Q)", "(b − xi ≤ 0) est dans (P and . . . and Q)", "solveur(a + b) = 0", "On a S tel que [xi := b](P and . . . and Q) = S"
  TYPE; // Stub.

symbol NRM29_1 [a b xi : El exp] [x1 xi_minus_1 xi_plus_1 xn : El idt] [H : El (list prd)] [P Q R S : El prd] :
  // Side conditions: "(xi + a ≤ 0) est dans (P and . . . and Q)", " (−xi + b ≤ 0) est dans (P and . . . and Q)", "solveur(a + b) = 0", "On a S tel que [xi := b](P and . . . and Q) = S"
  TYPE; // Stub.

symbol NRM30 [a b x : El exp] [H : El (list prd)] [P Q R S : El prd] :
  // Side conditions: "(a + x ≤ 0) est dans (P and . . . and Q)", "(b − x ≤ 0) est dans (P and . . . and Q)", "solveur(a + b) = 0", "On a S tel que [x := b](P and . . . and Q) = S"
  TYPE; // Stub.

symbol NRM30_1 [a b x : El exp] [H : El (list prd)] [P Q R S : El prd] :
  // Side conditions: "(x + a ≤ 0) est dans (P and . . . and Q)", " (−x + b ≤ 0) est dans (P and . . . and Q)", "solveur(a + b) = 0", "On a S tel que [x := b](P and . . . and Q) = S"
  TYPE; // Stub.

// ----------------------------------------------
// 5.13. Règles sur les égalités (Equality Rules)
// ----------------------------------------------
notation = infix right 4;
symbol EVR1 [H : El (list prd)] [E : El exp] [P : El prd] :
  ⟐ (H ⟝ not (E = E) => P);

symbol EVR11 [n m : Set] [H : El (list prd)] [P : El prd] : // n, m are natural numbers based on "n ∈ N, m ∈ N"
  // Side conditions: "n ∈ N", "m ∈ N", "n ≠ m"
  TYPE; // Stub for numerical comparison.

symbol EVR2 [H : El (list prd)] [E : El exp] :
  ⟐ (H ⟝ VRAI) →
  ⟐ (H ⟝ not (E = E));

symbol EVR3 [H : El (list prd)] [E : El exp] [P : El prd] :
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

symbol EAXM31 [H : El (list prd)] [E F : El exp] :
  Prf (elem (F = E) H) →
  ⟐ (H ⟝ (E = F));

symbol EAXM32 [H : El (list prd)] [E F : El exp] :
  Prf (elem (not (F = E)) H) →
  ⟐ (H ⟝ not (E = F));

// These rules relate to "P" (a predicate) and are named EIMP.
symbol EIMP51 [H : El (list prd)] [E F : El exp] [P : El prd] :
  Prf (elem (not (F = E)) H) →
  ⟐ (H ⟝ P) →
  ⟐ (H ⟝ not (E = F) => P);

symbol EIMP52 [H : El (list prd)] [E F : El exp] [P : El prd] :
  Prf (elem (F = E) H) →
  ⟐ (H ⟝ P) →
  ⟐ (H ⟝ (E = F) => P);

// These rules deal with equality of tuples/records, which implies some structured data types.
symbol EQC1 [H : El (list prd)] [a b c d : El exp] [P : El prd] : TYPE;
  //⟐ (H ⟝ (not (a = c) ∨ not (b = d)) => P) →
  //⟐ (H ⟝ not ((a ⨾ b) = (c ⨾ d)) => P); // Using '⨾' for tuple construction, consistent with vrb.
  // Assuming (a,b) is a tuple.

symbol EQC2 [H : El (list prd)] [a b c d : El exp] [P : El prd] : TYPE;
  //⟐ (H ⟝ (a = c) and (b = d) => P) →
  //⟐ (H ⟝ ((a ⨾ b) = (c ⨾ d)) => P);

// These rules relate to a specific "eql set" predicate, which suggests set equality.
symbol EQS1 [H : El (list prd)] [E F : El exp] [R : El prd] : TYPE;
  //⟐ (H ⟝ (E = F) => R) →
  //⟐ (H ⟝ (eql_set E F) => R); // Assuming eql_set is a predicate.

symbol EQS2 [H : El (list prd)] [E F : El exp] [R : El prd] : TYPE;
  //⟐ (H ⟝ VRAI => R) →
  //⟐ (H ⟝ not (eql_set E F) => R);

// These rules involve complex variable substitution and reduction to a simple equality.
symbol EAXM91 [x : El idt] [H : El (list prd)] [p q a b Q : El prd] : // p,q here are predicates (prds), not expressions (exp) for the equals comparison?
  // Side conditions: "forall x · not ( VRAI and p = q ) est dans H", "On a E tel que [x := E](q = p) se réduise à (a = b)"
  TYPE; // Stub.

symbol EAXM92 [x : El idt] [H : El (list prd)] [p q a b Q : El prd] :
  // Side conditions: "forall x · not ( VRAI and not (p = q) ) est dans H", "On a E tel que [x := E] (q = p) se réduise à (a = b)"
  TYPE; // Stub.

// These rules relate to substitution for variables.
symbol OPR1 [x : El idt] [H : El (list prd)] [P Q E : El prd] : // x is a variable (idt), E is an expression (exp)
  // Side conditions: "x est une variable", "x non libre dans H", "x non libre dans E", "Q est le résultat de la substitution [x := E] P"
  TYPE; // Stub.

symbol OPR2 [x : El idt] [H : El (list prd)] [P Q E : El prd] :
  // Side conditions: "x est une variable", "x non libre dans H", "x non libre dans E", "Q est le résultat de la substitution [x := E] P"
  TYPE; // Stub.

// These rules involve complex "replacement" (substitution) operations within predicates.
symbol ECTR1 [H : El (list prd)] [E F : El exp] [P Q R : El prd] :
  // Side conditions: "not Q est dans H", "le remplacement de E par F dans Q donne R", "R est dans H"
  TYPE; // Stub.

symbol ECTR2 [H : El (list prd)] [E F : El exp] [P Q R : El prd] :
  // Side conditions: "not Q est dans H", "le remplacement de E par F dans Q donne R", "R est dans H"
  TYPE; // Stub.

symbol ECTR3 [H : El (list prd)] [E F : El exp] [P Q R : El prd] :
  // Side conditions: "E = F est dans H", "le remplacement de E par F dans P donne R", "R est dans H"
  TYPE; // Stub.

symbol ECTR4 [H : El (list prd)] [E F : El exp] [P Q R : El prd] :
  // Side conditions: "F = E est dans H", "le remplacement de E par F dans P donne R", "R est dans H"
  TYPE; // Stub.

symbol ECTR5 [H : El (list prd)] [E F : El exp] [P Q R : El prd] :
  // Side conditions: "E = F est dans H", "le remplacement de E par F dans P donne R", "not R est dans H"
  TYPE; // Stub.

symbol ECTR6 [H : El (list prd)] [E F : El exp] [P Q R : El prd] :
  // Side conditions: "F = E est dans H", "le remplacement de E par F dans P donne R", "not R est dans H"
  TYPE; // Stub.






// ----------------------------------------------
// 5.15. Règles sur les booléens (Boolean Rules)
// ----------------------------------------------
// Assuming VRAI and VRAI are defined as propositions in the system.
// 'v' is likely a variable of boolean type or an an expression that evaluates to boolean.
//symbol BOOL11 [v : El exp] [H : El (list prd)] [P : El prd] :
//  ⟐ (((v = VRAI) ∷ (not (v = VRAI)) ∷ H) ⟝ P) →
//  ⟐ (H ⟝ (v = VRAI) => P);

//symbol BOOL12 [v : El exp] [H : El (list prd)] [P : El prd] :
//  ⟐ (((v = VRAI) ∷ (not (v = VRAI)) ∷ H) ⟝ P) →
//  ⟐ (H ⟝ (v = VRAI) => P);

//symbol BOOL21 [v : El exp] [H : El (list prd)] [P : El prd] :
//  ⟐ (H ⟝ (v = VRAI) => P) →
//  ⟐ (H ⟝ (VRAI = v) => P);

//symbol BOOL22 [v : El exp] [H : El (list prd)] [P : El prd] :
//  ⟐ (H ⟝ (v = VRAI) => P) →
//  ⟐ (H ⟝ (VRAI = v) => P);

//symbol BOOL31 [v : El exp] [H : El (list prd)] [P : El prd] :
//  ⟐ (H ⟝ (v = VRAI) => P) →
//  ⟐ (H ⟝ not (v = VRAI) => P);

//symbol BOOL32 [v : El exp] [H : El (list prd)] [P : El prd] :
//  ⟐ (H ⟝ (v = VRAI) => P) →
//  ⟐ (H ⟝ not (v = VRAI) => P);

//symbol BOOL41 [v : El exp] [H : El (list prd)] [P : El prd] :
//  ⟐ (H ⟝ (v = VRAI) => P) →
//  ⟐ (H ⟝ not (VRAI = v) => P);

//symbol BOOL42 [v : El exp] [H : El (list prd)] [P : El prd] :
//  ⟐ (H ⟝ (v = VRAI) => P) →
//  ⟐ (H ⟝ not (VRAI = v) => P);

//symbol BOOL51 [H : El (list prd)] [P : El prd] :
//  ⟐ (H ⟝ (VRAI = VRAI) => P);

//symbol BOOL52 [H : El (list prd)] [P : El prd] :
//  ⟐ (H ⟝ (VRAI = VRAI) => P);



// manual reconstruction of `01.trace`
//  [AXM1] &
//  [NOT1] &
//  [OR4] &
//  [IMP4] &
//  [AXM4] &
//  [OR4] &
//  [IMP4] &
//  [AND1] &
//   (not(p and q) => not(p) or not(q))
