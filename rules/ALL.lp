require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------############
// 5.7. Universal quantification
// ----------------------------------------------############
sequential symbol distinct : El (idt ⤳ idt ⤳ bool);
rule distinct $x $x ↪ ⊥
with distinct $x  _ ↪ ⊤;

symbol ? (x : El idt)  : El vrb ≔ x ∷ nil;
symbol ⨾ (x y : El idt) : El vrb ≔ x ∷ y ∷ nil;
notation ⨾ infix right 5;

symbol ALL1 [x y : El idt] [H : El (list prd)] [P R : El prd] :
  Prf (distinct x y) →
  ⟐ (H ⟝ not (forall (x ⨾ y) P) => R ) →
  ⟐ (H ⟝ not (forall (? x) (forall (? y) P)) => R );

symbol ALL2 [x y : El idt] [H : El (list prd)] [P : El prd] :
  Prf (distinct x y) →
  ⟐ (H ⟝ not (forall (x ⨾ y) P) ) →
  ⟐ (H ⟝ not (forall (? x) (forall (? y) P)));

symbol ALL3 [x y : El idt] [H : El (list prd)] [P R : El prd] :
  Prf (distinct x y) →
  ⟐ (H ⟝ (forall (x ⨾ y) P) => R ) →
  ⟐ (H ⟝ (forall (? x) (forall (? y) P)) => R );

symbol ALL4 [x y : El idt] [H : El (list prd)] [P : El prd] :
  Prf (distinct x y) →
  ⟐ (H ⟝ forall (x ⨾ y) P) →
  ⟐ (H ⟝ forall (? x) (forall (? y) P));

// This rule involves "x non libre dans R" (x not free in R) and potentially variable capture.
// A more robust mechanism for free variables and substitution is needed.
symbol ALL5 [x : El idt] [H : El (list prd)] [P R : El prd] :
  // Side condition: "x non libre dans R"
  // We'll need a mechanism for checking free variables.
  TYPE;
  // Side condition for the second ALL5 rule with different antecedents
  // "x est libre dans R", "y n'est libre ni dans P ni dans R", "S est le résultat de la substitution [x := y] P"
  // This requires a more complex rule for substitution and free variable checking.
  // TYPE; // Placeholder for the second ALL5 rule variant.

symbol ALL6 [x : El idt] [H : El (list prd)] [P : El prd] :
  ⟐ (H ⟝ (forall (? x) P) => FALSE) →
  ⟐ (H ⟝ not (forall (? x) P));

// These rules (ALL7, ALL7', ALL8, ALL8', ALL9, ALL9') use a '⇝' operator
// and a 'Résultat' column, indicating a more complex proof transformation or
// a result of applying the rule. The '♢ x' notation is not directly defined
// but likely relates to existential quantification or a special form of it.
symbol ALL7 [x : El idt] [H : El (list prd)] [P Q R : El prd] :
  // First variant: "x non libre dans H"
  // Antécédents: "( H ⊢ P ) ⇝ R", "H ⊢ ( ♢ x · R ) => Q"
  // Conséquent: "H ⊢ ( forall x · P ) => Q"
  TYPE;
  // Second variant: "x est libre dans H", "y n'est libre ni dans A ni dans H", "P est le résultat de la substitution [x := y] A"
  // Antécédents: "( H ⊢ P ) ⇝ R", "H ⊢ ( ♢ x · R ) => Q"
  // Conséquent: "H ⊢ ( forall x · A ) => Q"
  // TYPE;

symbol ALL7_prime [x : El idt] [H : El (list prd)] [P Q R S A : El prd] :
  // First variant: "x non libre dans H"
  // Antécédents: "( H ⊢ P ) ⇝ R", "( H ⊢ ( ♢ x · R ) => Q ) ⇝ S"
  // Conséquent: "H ⊢ ( forall x · P ) => Q"
  // Résultat: "S"
  TYPE;
  // Second variant: "x est libre dans H", "y n'est libre ni dans A ni dans H", "P est le résultat de la substitution [x := y] A"
  // Antécédents: "( H ⊢ P ) ⇝ R", "( H ⊢ ( ♢ x · R ) => Q ) ⇝ S"
  // Conséquent: "H ⊢ ( forall x · A ) => Q"
  // Résultat: "S"
  // TYPE;


symbol ALL8 [x : El idt] [H : El (list prd)] [P R : El prd] :
  // First variant: "x non libre dans H"
  // Antécédents: "H ⊢ P"
  // Conséquent: "H ⊢ forall x · P"
  TYPE;
  // Second variant: "x est libre dans H", "y n'est libre ni dans P ni dans H", "R est le résultat de la substitution [x := y] P"
  // Antécédents: "H ⊢ R"
  // Conséquent: "H ⊢ forall x · P"
  // TYPE;

symbol ALL8_prime [x y : El idt] [H : El (list prd)] [P Q R : El prd] :
  // First variant: "x non libre dans H"
  // Antécédents: "( H ⊢ P) ⇝ Q"
  // Conséquent: "H ⊢ forall x · P"
  // Résultat: "forall x · Q"
  TYPE;
  // Second variant: "x est libre dans H", "y n'est libre ni dans P ni dans H", "R est le résultat de la substitution [x := y] P"
  // Antécédents: "( H ⊢ R) ⇝ Q"
  // Conséquent: "H ⊢ forall x · P"
  // Résultat: "forall y · Q"
  // TYPE;

symbol ALL9 [x : El idt] [H : El (list prd)] [T Q : El prd] :
  // The '♡ x · T' notation is not defined, but might be related to 'forall2' or a specialized universal quantifier.
  ⟐ (T ∷ H ⟝ Q) → // H, ( forall x · T ) ⊢ Q
  ⟐ (H ⟝ (forall (? x) T) => Q); // The symbol '♡' in the antecedent corresponds to 'forall2' in the ASCII table, which is 'forall x'
  // It seems '♡' is equivalent to 'forall' for simple variable binding.
  // Assuming '♡' is just another notation for 'forall' as suggested by the ASCII table.

symbol ALL9_prime [x : El idt] [H : El (list prd)] [P Q R : El prd] :
  // Antécédents: "( H, ( forall x · P ) ⊢ Q ) ⇝ R"
  // Conséquent: "H ⊢ ( forall x · P ) => Q"
  // Résultat: "( forall x · P ) => R"
  // Requires understanding of '⇝' and 'Résultat'.
  TYPE;
