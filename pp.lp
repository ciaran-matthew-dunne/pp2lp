require open Logic.U.Set Logic.U.Prop Logic.U.Arrow;

symbol bool : Set;
rule El bool ↪ Prop;

injective symbol list : Set → Set;
symbol nil [a : Set] : El (list a);
symbol ∷ [a : Set] : El (a ⤳ list a ⤳ list a);
notation ∷ infix right 5;

sequential symbol elem [a : Set] : El (a ⤳ list a ⤳ bool);
rule (elem $x nil)        ↪ ⊥
with (elem $x ($x ∷ $xs)) ↪ ⊤
with (elem $x (_  ∷ $ys)) ↪ (elem $x $ys);

symbol ≈ [a : Set] : El (a ⤳ a ⤳ bool);
notation ≈ infix right 5;

// #################
// 3. Syntax
// #################
symbol String : TYPE;
builtin "String" ≔ String;

symbol idt : Set;
//rule El idt ↪ String;

symbol vrb : Set ≔ list idt;
symbol prd : Set;
symbol exp : Set;


symbol subst : El (idt ⤳ exp ⤳ prd);

symbol ∀ : El (vrb ⤳ prd ⤳ prd);
symbol ∃ : El (vrb ⤳ prd ⤳ prd);
symbol = : El (exp ⤳ exp ⤳ prd);
symbol != : El (exp ⤳ exp ⤳ prd);

symbol frm : Set;
injective symbol atom : El frm → El prd;
injective symbol ∧ : El (prd ⤳ prd ⤳ prd);
injective symbol ∨ : El (prd ⤳ prd ⤳ prd);
injective symbol ⇒ : El (prd ⤳ prd ⤳ prd);
injective symbol ⇔ : El (prd ⤳ prd ⤳ prd);
injective symbol ¬ : El (prd ⤳ prd);

notation ∧ infix left 2;
notation ∨ infix left 2;
notation ⇒ infix left 2;
notation ⇔ infix left 1;
notation ¬ prefix 3;

symbol ♢ : El (vrb ⤳ prd ⤳ prd);
symbol ♡ : El (vrb ⤳ prd ⤳ prd);

symbol ≤ : El (exp ⤳ exp ⤳ prd); notation ≤ infix 5;
symbol < : El (exp ⤳ exp ⤳ prd); notation < infix 5;
symbol ≪ : El (exp ⤳ exp ⤳ prd); notation < infix 5;

symbol 𝟎 : El (exp);
symbol 𝟏 : El (exp);
symbol ⨪ : El (exp ⤳ exp);
symbol + : El (exp ⤳ exp ⤳ exp); notation + infix 5;
symbol - : El (exp ⤳ exp ⤳ exp); notation - infix 5;

symbol solveur [a : Set] : El (a ⤳ a);

symbol ℕ : El exp;
symbol ∈ : El (exp ⤳ exp ⤳ prd); notation ∈ infix 5;




// ## sequents
symbol sequent : Set;
injective symbol ⟝ : El (list prd ⤳ prd ⤳ sequent);
notation ⟝ infix 0;



injective symbol ✓ : El sequent → TYPE;

symbol thm (p : El prd) : TYPE ≔ ✓ (nil ⟝ p);

// Boolean constants (implied from rules)
symbol TRUE : El prd;
symbol FALSE : El prd;

// #################
// 5.1. Conjunction
// #################
symbol AND1 [H : El (list prd)] [P Q R : El prd] :
  ✓ (H ⟝ ¬ Q ⇒ R) →
  ✓ (H ⟝ ¬ P ⇒ R) →
  ✓ (H ⟝ ¬ (P ∧ Q) ⇒ R);

symbol AND2 [H : El (list prd)] [P Q : El prd] :
  ✓ (H ⟝ P ⇒ ¬ Q) →
  ✓ (H ⟝ ¬ (P ∧ Q));

symbol AND3 [H : El (list prd)] [P Q R : El prd] :
  ✓ (H ⟝ P ⇒ (Q ⇒ R)) →
  ✓ (H ⟝ (P ∧ Q) ⇒ R);

symbol AND4 [H : El (list prd)] [P Q : El prd] :
  ✓ (H ⟝ Q) → // H ⊢ Q is the second antecedent
  ✓ (H ⟝ P) → // H ⊢ P is the first antecedent
  ✓ (H ⟝ (P ∧ Q));

// This rule seems to involve pattern matching within a conjunction,
// and a substitution-like operation that is not directly captured by
// the current primitives.
symbol AND5 [H : El (list prd)] [P Q R A B : El prd] :
  // Antécédents: "P ∧ · · · Contient A", "H ⊢ P ∧ · · · ∧ (A ⇒ B) ∧ · · · ⇒ R"
  // Conséquent: "H ⊢ P ∧ · · · ∧ B ∧ · · · ⇒ R"
  // Requires a more sophisticated pattern matching and replacement mechanism.
  // Stub for now.
  TYPE;
// #################
// 5.2. Disjunction
// #################
symbol OR1 [H : El (list prd)] [P Q R : El prd] :
  ✓ (H ⟝ ¬ P ⇒ (¬ Q ⇒ R)) →
  ✓ (H ⟝ ¬ (P ∨ Q) ⇒ R);

symbol OR2 [H : El (list prd)] [P Q : El prd] :
  ✓ (H ⟝ ¬ Q) →
  ✓ (H ⟝ ¬ P) →
  ✓ (H ⟝ ¬ (P ∨ Q));

symbol OR3 [H : El (list prd)] [P Q R : El prd] :
  ✓ (H ⟝ Q ⇒ R) →
  ✓ (H ⟝ P ⇒ R) →
  ✓ (H ⟝ (P ∨ Q) ⇒ R);

symbol OR4 [H : El (list prd)] [P Q : El prd] :
  ✓ (H ⟝ ¬ P ⇒ Q) →
  ✓ (H ⟝ (P ∨ Q));

// #################
// 5.3. Implication
// #################

symbol IMP1 [H : El (list prd)] [P Q R : El prd] :
  ✓ (H ⟝ P ⇒ (¬ Q ⇒ R)) →
  ✓ (H ⟝ ¬ (P ⇒ Q) ⇒ R);

symbol IMP2 [H : El (list prd)] [P Q : El prd] :
  ✓ (H ⟝ ¬ Q) →
  ✓ (H ⟝ P) → // This is "H ⊢ P" in the antecedent
  ✓ (H ⟝ ¬ (P ⇒ Q));

symbol IMP3 [H : El (list prd)] [P Q R : El prd] :
  ✓ (H ⟝ Q ⇒ R) →
  ✓ (H ⟝ ¬ P ⇒ R) →
  ✓ (H ⟝ (P ⇒ Q) ⇒ R);

symbol IMP4 [H : El (list prd)] [P Q : El prd] :
  ✓ (P ∷ H ⟝ Q) → ✓ (H ⟝ P ⇒ Q);

symbol IMP5 [H : El (list prd)] [P Q : El prd] :
  Prf (elem P H) → // Side condition: "P est dans H"
  ✓ (H ⟝ Q) →
  ✓ (H ⟝ P ⇒ Q);

// from (H,P ⟝ Q) ⇀ R and (H ⟝ P ⇒ Q)
// infer (H ⟝ P ⇒ R)
// This rule has a 'Résultat' (Result) column, which is not directly representable
// in the current syntax. It implies a transformation or a return value from the proof rule.
symbol IMP4' [H : El (list prd)] [P Q R S : El prd] :
  // Antécédents: "(H,P ⊢ Q) ⇝ R"
  // Conséquent: "H ⊢ P ⇒ Q"
  // Résultat: "P ⇒ R"
  // This rule requires understanding of the '⇝' operator and 'Résultat' column.
  TYPE;

// #################
// 5.4. Equivalence
// #################
symbol EQV1 [H : El (list prd)] [P Q R : El prd] :
  ✓ (H ⟝ P ⇒ (¬ Q ⇒ R)) →
  ✓ (H ⟝ ¬ P ⇒ (Q ⇒ R)) →
  ✓ (H ⟝ ¬ (P ⇔ Q) ⇒ R);

symbol EQV2 [H : El (list prd)] [P Q : El prd] :
  ✓ (H ⟝ P ⇒ ¬ Q) →
  ✓ (H ⟝ ¬ Q ⇒ P) →
  ✓ (H ⟝ ¬ (P ⇔ Q));

symbol EQV3 [H : El (list prd)] [P Q R : El prd] :
  ✓ (H ⟝ P ⇒ (Q ⇒ R)) →
  ✓ (H ⟝ ¬ P ⇒ (¬ Q ⇒ R)) →
  ✓ (H ⟝ (P ⇔ Q) ⇒ R);

symbol EQV4 [H : El (list prd)] [P Q : El prd] :
  ✓ (H ⟝ P ⇒ Q) →
  ✓ (H ⟝ Q ⇒ P) →
  ✓ (H ⟝ (P ⇔ Q));

// #################
// 5.5. Negation
// #################
symbol NOT1 [H : El (list prd)] [P R : El prd] :
  ✓ (H ⟝ P ⇒ R) →
  ✓ (H ⟝ ¬ ¬ P ⇒ R);

symbol NOT2 [H : El (list prd)] [P : El prd] : // R is not present in the Conséquent of NOT2
  ✓ (H ⟝ P) →
  ✓ (H ⟝ ¬ ¬ P); // The source defines H ⊢ ¬¬P, not H ⊢ ¬¬P ⇒ R.

// #################
// 5.6. Axioms
// #################
symbol AXM1 [H : El (list prd)] [P Q : El prd] :
  Prf (elem (¬ P) H) →
  ✓ (H ⟝ P ⇒ Q);

symbol AXM2 [H : El (list prd)] [P Q : El prd] :
  Prf (elem P H) →
  ✓ (H ⟝ ¬ P ⇒ Q);

symbol AXM3 [H : El (list prd)] [P : El prd] :
  Prf (elem P H) →
  ✓ (H ⟝ P);

symbol AXM4 [H : El (list prd)] [P R : El prd] :
  Prf (elem R H) →
  ✓ (H ⟝ P ⇒ R);

symbol AXM5 [H : El (list prd)] [P Q R : El prd] :
  Prf (elem (¬ Q) H) →
  ✓ (H ⟝ P ⇒ (Q ⇒ R));

symbol AXM6 [H : El (list prd)] [P Q R : El prd] :
  Prf (elem Q H) →
  ✓ (H ⟝ P ⇒ (¬ Q ⇒ R));

symbol AXM7 [H : El (list prd)] [P : El prd] :
  ✓ (H ⟝ P ⇒ P);

// This rule seems to involve pattern matching and substitution within a conjunction,
// similar to AND5.
symbol AXM8 [H : El (list prd)] [P R : El prd] :
  // Antécédents: "P ∧ · · · contient R"
  // Conséquent: "H ⊢ P ∧ · · · ⇒ R"
  // This rule implies some kind of simplification or reduction within a conjunction.
  TYPE;

// This rule involves existential quantification and substitution not directly expressible.
symbol AXM9 [H : El (list prd)] [R Q : El prd] :
  // Antécédents: "∀ x · ¬ ( VRAI ∧ P ) est dans H", "On a E tel que [x := E] P = R"
  // Conséquent: "H ⊢ R ⇒ Q"
  // This rule appears to be about existential instantiation or a form of it.
  TYPE;

// #############################
// 5.7. Universal quantification
// #############################
sequential symbol distinct : El (idt ⤳ idt ⤳ bool);
rule distinct $x $x ↪ ⊥
with distinct $x _ ↪ ⊤ ;

symbol ? (x : El idt) : El vrb ≔ x ∷ nil;
symbol ⨾ (x y : El idt) : El vrb ≔ x ∷ y ∷ nil;
notation ⨾ infix right 5;

symbol ALL1 [x y : El idt] [H : El (list prd)] [P R : El prd] :
  Prf (distinct x y) →
  ✓ (H ⟝ ¬ (∀ (x ⨾ y) P) ⇒ R ) →
  ✓ (H ⟝ ¬ (∀ (? x) (∀ (? y) P)) ⇒ R );

symbol ALL2 [x y : El idt] [H : El (list prd)] [P : El prd] :
  Prf (distinct x y) →
  ✓ (H ⟝ ¬ (∀ (x ⨾ y) P) ) →
  ✓ (H ⟝ ¬ (∀ (? x) (∀ (? y) P)));

symbol ALL3 [x y : El idt] [H : El (list prd)] [P R : El prd] :
  Prf (distinct x y) →
  ✓ (H ⟝ (∀ (x ⨾ y) P) ⇒ R ) →
  ✓ (H ⟝ (∀ (? x) (∀ (? y) P)) ⇒ R );

symbol ALL4 [x y : El idt] [H : El (list prd)] [P : El prd] :
  Prf (distinct x y) →
  ✓ (H ⟝ ∀ (x ⨾ y) P) →
  ✓ (H ⟝ ∀ (? x) (∀ (? y) P));

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
  ✓ (H ⟝ (∀ (? x) P) ⇒ FALSE) →
  ✓ (H ⟝ ¬ (∀ (? x) P));

// These rules (ALL7, ALL7', ALL8, ALL8', ALL9, ALL9') use a '⇝' operator
// and a 'Résultat' column, indicating a more complex proof transformation or
// a result of applying the rule. The '♢ x' notation is not directly defined
// but likely relates to existential quantification or a special form of it.
symbol ALL7 [x : El idt] [H : El (list prd)] [P Q R : El prd] :
  // First variant: "x non libre dans H"
  // Antécédents: "( H ⊢ P ) ⇝ R", "H ⊢ ( ♢ x · R ) ⇒ Q"
  // Conséquent: "H ⊢ ( ∀ x · P ) ⇒ Q"
  TYPE;
  // Second variant: "x est libre dans H", "y n'est libre ni dans A ni dans H", "P est le résultat de la substitution [x := y] A"
  // Antécédents: "( H ⊢ P ) ⇝ R", "H ⊢ ( ♢ x · R ) ⇒ Q"
  // Conséquent: "H ⊢ ( ∀ x · A ) ⇒ Q"
  // TYPE;

symbol ALL7_prime [x : El idt] [H : El (list prd)] [P Q R S A : El prd] :
  // First variant: "x non libre dans H"
  // Antécédents: "( H ⊢ P ) ⇝ R", "( H ⊢ ( ♢ x · R ) ⇒ Q ) ⇝ S"
  // Conséquent: "H ⊢ ( ∀ x · P ) ⇒ Q"
  // Résultat: "S"
  TYPE;
  // Second variant: "x est libre dans H", "y n'est libre ni dans A ni dans H", "P est le résultat de la substitution [x := y] A"
  // Antécédents: "( H ⊢ P ) ⇝ R", "( H ⊢ ( ♢ x · R ) ⇒ Q ) ⇝ S"
  // Conséquent: "H ⊢ ( ∀ x · A ) ⇒ Q"
  // Résultat: "S"
  // TYPE;


symbol ALL8 [x : El idt] [H : El (list prd)] [P R : El prd] :
  // First variant: "x non libre dans H"
  // Antécédents: "H ⊢ P"
  // Conséquent: "H ⊢ ∀ x · P"
  TYPE;
  // Second variant: "x est libre dans H", "y n'est libre ni dans P ni dans H", "R est le résultat de la substitution [x := y] P"
  // Antécédents: "H ⊢ R"
  // Conséquent: "H ⊢ ∀ x · P"
  // TYPE;

symbol ALL8_prime [x y : El idt] [H : El (list prd)] [P Q R : El prd] :
  // First variant: "x non libre dans H"
  // Antécédents: "( H ⊢ P) ⇝ Q"
  // Conséquent: "H ⊢ ∀ x · P"
  // Résultat: "∀ x · Q"
  TYPE;
  // Second variant: "x est libre dans H", "y n'est libre ni dans P ni dans H", "R est le résultat de la substitution [x := y] P"
  // Antécédents: "( H ⊢ R) ⇝ Q"
  // Conséquent: "H ⊢ ∀ x · P"
  // Résultat: "∀ y · Q"
  // TYPE;

symbol ALL9 [x : El idt] [H : El (list prd)] [T Q : El prd] :
  // The '♡ x · T' notation is not defined, but might be related to 'forall2' or a specialized universal quantifier.
  ✓ (T ∷ H ⟝ Q) → // H, ( ∀ x · T ) ⊢ Q
  ✓ (H ⟝ (∀ (? x) T) ⇒ Q); // The symbol '♡' in the antecedent corresponds to 'forall2' in the ASCII table, which is '∀ x'
  // It seems '♡' is equivalent to '∀' for simple variable binding.
  // Assuming '♡' is just another notation for '∀' as suggested by the ASCII table.

symbol ALL9_prime [x : El idt] [H : El (list prd)] [P Q R : El prd] :
  // Antécédents: "( H, ( ∀ x · P ) ⊢ Q ) ⇝ R"
  // Conséquent: "H ⊢ ( ∀ x · P ) ⇒ Q"
  // Résultat: "( ∀ x · P ) ⇒ R"
  // Requires understanding of '⇝' and 'Résultat'.
  TYPE;

// #############################
// 5.8. Existential quantification
// #############################
// The '∃' symbol is assumed based on context and common logic.
// The rules for existential quantification often mirror universal quantification rules for negated forms.

symbol XST1 [x y : El idt] [H : El (list prd)] [P R : El prd] :
  Prf (distinct x y) →
  ✓ (H ⟝ ¬ (∃ (x ⨾ y) P) ⇒ R ) →
  ✓ (H ⟝ ¬ (∃ (? x) (∃ (? y) P)) ⇒ R );

symbol XST2 [x y : El idt] [H : El (list prd)] [P : El prd] :
  Prf (distinct x y) →
  ✓ (H ⟝ ¬ (∃ (x ⨾ y) P) ) →
  ✓ (H ⟝ ¬ (∃ (? x) (∃ (? y) P)));

symbol XST3 [x y : El idt] [H : El (list prd)] [P R : El prd] :
  Prf (distinct x y) →
  ✓ (H ⟝ (∃ (x ⨾ y) P) ⇒ R ) →
  ✓ (H ⟝ (∃ (? x) (∃ (? y) P)) ⇒ R );

symbol XST4 [x y : El idt] [H : El (list prd)] [P : El prd] :
  Prf (distinct x y) →
  ✓ (H ⟝ ∃ (x ⨾ y) P) →
  ✓ (H ⟝ ∃ (? x) (∃ (? y) P));

symbol XST5 [x : El idt] [H : El (list prd)] [P R : El prd] :
  ✓ (H ⟝ (∀ (? x) ¬ P) ⇒ R) →
  ✓ (H ⟝ ¬ (∃ (? x) P) ⇒ R);

symbol XST51 [x : El idt] [H : El (list prd)] [P R : El prd] :
  ✓ (H ⟝ (∀ (? x) P) ⇒ R) →
  ✓ (H ⟝ ¬ (∃ (? x) ¬ P) ⇒ R);

symbol XST6 [x : El idt] [H : El (list prd)] [P : El prd] :
  ✓ (H ⟝ ∀ (? x) ¬ P) →
  ✓ (H ⟝ ¬ (∃ (? x) P));

symbol XST61 [x : El idt] [H : El (list prd)] [P : El prd] :
  ✓ (H ⟝ ∀ (? x) P) →
  ✓ (H ⟝ ¬ (∃ (? x) ¬ P));

// Similar to ALL5, involves free variables and substitution.
symbol XST7 [x : El idt] [H : El (list prd)] [P R Q : El prd] :
  // First variant: "x non libre dans R"
  // Antécédents: "H ⊢ ∀ x · ( P ⇒ R )"
  // Conséquent: "H ⊢ ( ∃ x · P ) ⇒ R"
  TYPE;
  // Second variant: "x est libre dans R", "y n'est libre ni dans P ni dans R", "Q est le résultat de la substitution [x := y] P"
  // Antécédents: "H ⊢ ∀ y · ( Q ⇒ R )"
  // Conséquent: "H ⊢ ( ∃ x · P ) ⇒ R"
  // TYPE;

// These rules involve the '⇝' operator and possibly existential discharge.
symbol XST8 [x y : El idt] [H : El (list prd)] [P R A : El prd] :
  // First variant: "x non libre dans H"
  // Antécédents: "( H ⊢ ¬ P ) ⇝ R", "H ⊢ ( ∀ x · R ) ⇒ FAUX"
  // Conséquent: "H ⊢ ∃ x · P"
  TYPE;
  // Second variant: "x est libre dans H", "y n'est libre ni dans A ni dans H", "P est le résultat de la substitution [x := y] A"
  // Antécédents: "( H ⊢ ¬ P ) ⇝ R", "H ⊢ ( ∀ x · R ) ⇒ FAUX"
  // Conséquent: "H ⊢ ( ∃ x · A )"
  // TYPE;

// #################
// 5.9. Vrai et Faux (True and False)
// #################
symbol VR1 [H : El (list prd)] [R : El prd] :
  ✓ (H ⟝ ¬ TRUE ⇒ R);

symbol VR2 [H : El (list prd)] :
  ✓ (H ⟝ FALSE) →
  ✓ (H ⟝ ¬ TRUE);

symbol VR3 [H : El (list prd)] [R : El prd] :
  ✓ (H ⟝ R) →
  ✓ (H ⟝ TRUE ⇒ R);

symbol VR4 [H : El (list prd)] :
  ✓ (H ⟝ TRUE);

symbol FX1 [H : El (list prd)] [R : El prd] :
  ✓ (H ⟝ R) →
  ✓ (H ⟝ ¬ FALSE ⇒ R);

symbol FX2 [H : El (list prd)] :
  ✓ (H ⟝ ¬ FALSE);

symbol FX3 [H : El (list prd)] [R : El prd] :
  ✓ (H ⟝ FALSE ⇒ R);

// #################
// 5.10. Règles STOP
// #################
symbol STOP [H : El (list prd)] [P : El prd] :
  // Side condition: "P n'est pas le prédicat FAUX"
  ✓ (H ⟝ ¬ P ⇒ FALSE) →
  ✓ (H ⟝ P);

// This rule has a 'Résultat' column.
symbol STOP_prime [H : El (list prd)] [P : El prd] :
  // Antécédents: "H ⊢ P"
  // Conséquent: "P" (This consequent format is unusual for sequents, suggesting P itself is the result of applying the rule)
  // Résultat: "P"
  TYPE;

// #################
// 5.11. Règle INS (Instantiation)
// #################
symbol INS [H : El (list prd)] [Q1 Q2 Qn : El prd] : // Q1, Q2, ..., Qn are determined by "Détermination des instanciations"
  // Side condition: "Détermination des instanciations Q1, Q2, . . ., Qn"
  // This implies some form of meta-level computation or an external instantiation mechanism.
  //✓ (H ⟝ Q1 ⇒ (Q2 ⇒ ... ⇒ (Qn ⇒ FALSE) ...)) →
  //✓ (H ⟝ FALSE);
  TYPE;
// #################
// 5.12. Normalisation
// #################
// These rules heavily rely on "non libre dans" (not free in), substitution,
// and the '♢' operator (which likely corresponds to 'exists' or a specific type of 'forall2' from the ASCII table).
// Given the complexity of free variable checking, substitution, and the '♢' symbol (which is represented as 'forall2' in the ASCII table but sometimes used for existential quantifiers by convention or specific systems),
// these rules will be stubs.

symbol NRM1 [x : El idt] [H : El (list prd)] [P S : El prd] :
  // Side condition: "x non libre dans P"
  ✓ (H ⟝ P ⇒ S) →
  ✓ (H ⟝ (∀ (? x) P) ⇒ S); // Assuming ♢ x is ∀ x based on the ASCII table
  // However, the NRM rules seem to be about pushing quantifiers through implications,
  // where '♢' often refers to existential (e.g., 'exists x') or a general 'forall' form that can be re-arranged.
  // I will use '∀' for '♢' based on the ASCII table provided.
  // The '♢' symbol is shown as 'forall2' in the ASCII table, which maps to '∀'.
  // However, the behavior of some NRM rules, especially with conjunctions (NRM7),
  // suggests '♢' might act like an existential quantifier in certain contexts (distributing over conjunctions).
  // For consistency with the provided table, I'll use ∀ here.
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
  TYPE; // Stub due to '♢' interpretation and VRAI (TRUE).

symbol NRM12 [x : El idt] [H : El (list prd)] [P Q R : El prd] :
  TYPE; // Stub due to '♢' interpretation.

symbol NRM13 [x : El idt] [H : El (list prd)] [P Q R : El prd] :
  TYPE; // Stub due to '♢' interpretation.

symbol NRM14 [x : El idt] [H : El (list prd)] [P R : El prd] :
  TYPE; // Stub due to '♢' interpretation and VRAI.

symbol NRM15 [x : El idt] [H : El (list prd)] [P R : El prd] :
  TYPE; // Stub due to '♢' interpretation and VRAI.

symbol NRM16 [x : El idt] [H : El (list prd)] [P Q : El prd] :
  Prf (elem (∀ (? x) P) H) → // "∀ x · P est dans H"
  ✓ (H ⟝ (∀ (? x) P) ⇒ Q);

// These rules involve existential instantiation and substitution, which are not directly supported.
symbol NRM17 [x y : El idt] [H : El (list prd)] [P Q R E : El prd] :
  // Side conditions: "∀ x · ¬ ( VRAI ∧ P ) est dans H", "On a E tel que [x := E] P = R"
  TYPE; // Stub.

symbol NRM18 [x y : El idt] [H : El (list prd)] [P Q R E : El prd] :
  // Side conditions: "∀ x · ¬ ( VRAI ∧ ¬ P ) est dans H", "On a E tel que [x := E] (P) = R"
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
  // Side condition: "P n'est pas de la forme A ∧ B"
  TYPE; // Stub.

symbol NRM25 [x : El idt] [H : El (list prd)] [P : El prd] :
  // Side condition: "x non libre dans P"
  ✓ (H ⟝ P) →
  ✓ (H ⟝ ∀ (? x) P); // Forall2 (x) corresponds to ∀ x
  // Assuming 'forall2' is also syntactic sugar for universal quantification.

symbol NRM26 [x y : El idt] [H : El (list prd)] [P : El prd] :
  // Side condition: "y non libre dans P"
  ✓ (H ⟝ ∀ (x ∷ nil) P) → // forall2 (x, . . .) · P
  ✓ (H ⟝ ∀ (x ∷ y ∷ nil) P); // forall2 (x, y, . . .) · P
  // This rule appears to be for adding universally quantified variables that are not free in P.
  //TYPE; // Stub for more general list of variables.

// These normalization rules involve arithmetic inequalities, variable replacement,
// and a "solver" function, which are beyond the scope of current primitives.
symbol NRM27 [x1 xi xn : El idt] [H : El (list prd)] [P Q R : El prd] :
  // Side conditions: "(xi ≤ 0) est dans (P ∧ . . . ∧ Q)", " (−xi ≤ 0) est dans (P ∧ . . . ∧ Q)", "On a R tel que [xi := 0](P ∧ . . . ∧ Q) = R"
  TYPE; // Stub.

symbol NRM28 [x : El idt] [H : El (list prd)] [P Q R S : El prd] :
  // Side conditions: "(x ≤ 0) est dans (P ∧ . . . ∧ Q)", " (−x ≤ 0) est dans (P ∧ . . . ∧ Q)", "On a S tel que [x := 0](P ∧ . . . ∧ Q) = S"
  TYPE; // Stub.

symbol NRM29 [a b xi : El exp] [x1 xi_minus_1 xi_plus_1 xn : El idt] [H : El (list prd)] [P Q R S : El prd] :
  // Side conditions: "(a + xi ≤ 0) est dans (P ∧ . . . ∧ Q)", "(b − xi ≤ 0) est dans (P ∧ . . . ∧ Q)", "solveur(a + b) = 0", "On a S tel que [xi := b](P ∧ . . . ∧ Q) = S"
  TYPE; // Stub.

symbol NRM29_1 [a b xi : El exp] [x1 xi_minus_1 xi_plus_1 xn : El idt] [H : El (list prd)] [P Q R S : El prd] :
  // Side conditions: "(xi + a ≤ 0) est dans (P ∧ . . . ∧ Q)", " (−xi + b ≤ 0) est dans (P ∧ . . . ∧ Q)", "solveur(a + b) = 0", "On a S tel que [xi := b](P ∧ . . . ∧ Q) = S"
  TYPE; // Stub.

symbol NRM30 [a b x : El exp] [H : El (list prd)] [P Q R S : El prd] :
  // Side conditions: "(a + x ≤ 0) est dans (P ∧ . . . ∧ Q)", "(b − x ≤ 0) est dans (P ∧ . . . ∧ Q)", "solveur(a + b) = 0", "On a S tel que [x := b](P ∧ . . . ∧ Q) = S"
  TYPE; // Stub.

symbol NRM30_1 [a b x : El exp] [H : El (list prd)] [P Q R S : El prd] :
  // Side conditions: "(x + a ≤ 0) est dans (P ∧ . . . ∧ Q)", " (−x + b ≤ 0) est dans (P ∧ . . . ∧ Q)", "solveur(a + b) = 0", "On a S tel que [x := b](P ∧ . . . ∧ Q) = S"
  TYPE; // Stub.

// #################
// 5.13. Règles sur les égalités (Equality Rules)
// #################
notation = infix right 4;
symbol EVR1 [H : El (list prd)] [E : El exp] [P : El prd] :
  ✓ (H ⟝ ¬ (E = E) ⇒ P);

symbol EVR11 [n m : Set] [H : El (list prd)] [P : El prd] : // n, m are natural numbers based on "n ∈ N, m ∈ N"
  // Side conditions: "n ∈ N", "m ∈ N", "n ≠ m"
  TYPE; // Stub for numerical comparison.

symbol EVR2 [H : El (list prd)] [E : El exp] :
  ✓ (H ⟝ FALSE) →
  ✓ (H ⟝ ¬ (E = E));

symbol EVR3 [H : El (list prd)] [E : El exp] [P : El prd] :
  ✓ (H ⟝ P) →
  ✓ (H ⟝ (E = E) ⇒ P);

symbol EVR4 [H : El (list prd)] [E : El exp] :
  ✓ (H ⟝ (E = E));

symbol EAXM1 [H : El (list prd)] [E F : El exp] [P : El prd] :
  Prf (elem (¬ (F = E)) H) →
  ✓ (H ⟝ (E = F) ⇒ P);

symbol EAXM2 [H : El (list prd)] [E F : El exp] [P : El prd] :
  Prf (elem (F = E) H) →
  ✓ (H ⟝ ¬ (E = F) ⇒ P);

symbol EAXM31 [H : El (list prd)] [E F : El exp] :
  Prf (elem (F = E) H) →
  ✓ (H ⟝ (E = F));

symbol EAXM32 [H : El (list prd)] [E F : El exp] :
  Prf (elem (¬ (F = E)) H) →
  ✓ (H ⟝ ¬ (E = F));

// These rules relate to "P" (a predicate) and are named EIMP.
symbol EIMP51 [H : El (list prd)] [E F : El exp] [P : El prd] :
  Prf (elem (¬ (F = E)) H) →
  ✓ (H ⟝ P) →
  ✓ (H ⟝ ¬ (E = F) ⇒ P);

symbol EIMP52 [H : El (list prd)] [E F : El exp] [P : El prd] :
  Prf (elem (F = E) H) →
  ✓ (H ⟝ P) →
  ✓ (H ⟝ (E = F) ⇒ P);

// These rules deal with equality of tuples/records, which implies some structured data types.
symbol EQC1 [H : El (list prd)] [a b c d : El exp] [P : El prd] : TYPE;
  //✓ (H ⟝ (¬ (a = c) ∨ ¬ (b = d)) ⇒ P) →
  //✓ (H ⟝ ¬ ((a ⨾ b) = (c ⨾ d)) ⇒ P); // Using '⨾' for tuple construction, consistent with vrb.
  // Assuming (a,b) is a tuple.

symbol EQC2 [H : El (list prd)] [a b c d : El exp] [P : El prd] : TYPE;
  //✓ (H ⟝ (a = c) ∧ (b = d) ⇒ P) →
  //✓ (H ⟝ ((a ⨾ b) = (c ⨾ d)) ⇒ P);

// These rules relate to a specific "eql set" predicate, which suggests set equality.
symbol EQS1 [H : El (list prd)] [E F : El exp] [R : El prd] : TYPE;
  //✓ (H ⟝ (E = F) ⇒ R) →
  //✓ (H ⟝ (eql_set E F) ⇒ R); // Assuming eql_set is a predicate.

symbol EQS2 [H : El (list prd)] [E F : El exp] [R : El prd] : TYPE;
  //✓ (H ⟝ FALSE ⇒ R) →
  //✓ (H ⟝ ¬ (eql_set E F) ⇒ R);

// These rules involve complex variable substitution and reduction to a simple equality.
symbol EAXM91 [x : El idt] [H : El (list prd)] [p q a b Q : El prd] : // p,q here are predicates (prds), not expressions (exp) for the equals comparison?
  // Side conditions: "∀ x · ¬ ( VRAI ∧ p = q ) est dans H", "On a E tel que [x := E](q = p) se réduise à (a = b)"
  TYPE; // Stub.

symbol EAXM92 [x : El idt] [H : El (list prd)] [p q a b Q : El prd] :
  // Side conditions: "∀ x · ¬ ( VRAI ∧ ¬ (p = q) ) est dans H", "On a E tel que [x := E] (q = p) se réduise à (a = b)"
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
  // Side conditions: "¬ Q est dans H", "le remplacement de E par F dans Q donne R", "R est dans H"
  TYPE; // Stub.

symbol ECTR2 [H : El (list prd)] [E F : El exp] [P Q R : El prd] :
  // Side conditions: "¬ Q est dans H", "le remplacement de E par F dans Q donne R", "R est dans H"
  TYPE; // Stub.

symbol ECTR3 [H : El (list prd)] [E F : El exp] [P Q R : El prd] :
  // Side conditions: "E = F est dans H", "le remplacement de E par F dans P donne R", "R est dans H"
  TYPE; // Stub.

symbol ECTR4 [H : El (list prd)] [E F : El exp] [P Q R : El prd] :
  // Side conditions: "F = E est dans H", "le remplacement de E par F dans P donne R", "R est dans H"
  TYPE; // Stub.

symbol ECTR5 [H : El (list prd)] [E F : El exp] [P Q R : El prd] :
  // Side conditions: "E = F est dans H", "le remplacement de E par F dans P donne R", "¬ R est dans H"
  TYPE; // Stub.

symbol ECTR6 [H : El (list prd)] [E F : El exp] [P Q R : El prd] :
  // Side conditions: "F = E est dans H", "le remplacement de E par F dans P donne R", "¬ R est dans H"
  TYPE; // Stub.




// #################
// 5.14. Règles sur l'arithmétique (Arithmetic Rules)
// #################
// These rules involve numeric comparisons, arithmetic operations, and a "solver" function.
// They also involve expressions, which need to be defined as distinct from predicates for comparison operators like '<='


symbol AR1 [H : El (list prd)] [E : El exp] [R : El prd] :
  ✓ (H ⟝ R) →
  ✓ (H ⟝ (E ≤ E) ⇒ R); // Assuming ≤ is a binary operator on expressions producing a predicate.

symbol AR2 [a b : El exp] [H : El (list prd)] [R : El prd] :
  // Side conditions: "a est numérique", "b est numérique", "a > b"
  TYPE; // Stub due to numeric specific conditions.

symbol AR3 [a : El exp] [H : El (list prd)] [R : El prd] :
  ✓ (H ⟝ ((𝟏 - a) ≤ 𝟎) ⇒ R) →
  ✓ (H ⟝ ¬ (a ≤ 𝟎) ⇒ R);

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
  ✓ (H ⟝ (solveur P) ⇒ R) →
  ✓ (H ⟝ P ⇒ R);

symbol AR11 [x : El exp] [H : El (list prd)] [P : El prd] :
  ✓ (H ⟝ ¬ (x ≤ x) ⇒ P);

symbol AR12 [a b : El exp] [H : El (list prd)] [P : El prd] : TYPE;
  //✓ ((a ≤ b) ∷ H ⟝ P) → // H,(a ≤ b) ⊢ P
  //✓ (H ⟝ ((a ≪ b) ⇒ P)); // Assuming ≪ means strictly less than.



// #################
// 5.15. Règles sur les booléens (Boolean Rules)
// #################
// Assuming TRUE and FALSE are defined as propositions in the system.
// 'v' is likely a variable of boolean type or an an expression that evaluates to boolean.
//symbol BOOL11 [v : El exp] [H : El (list prd)] [P : El prd] :
//  ✓ (((v = TRUE) ∷ (¬ (v = FALSE)) ∷ H) ⟝ P) →
//  ✓ (H ⟝ (v = TRUE) ⇒ P);

//symbol BOOL12 [v : El exp] [H : El (list prd)] [P : El prd] :
//  ✓ (((v = FALSE) ∷ (¬ (v = TRUE)) ∷ H) ⟝ P) →
//  ✓ (H ⟝ (v = FALSE) ⇒ P);

//symbol BOOL21 [v : El exp] [H : El (list prd)] [P : El prd] :
//  ✓ (H ⟝ (v = TRUE) ⇒ P) →
//  ✓ (H ⟝ (TRUE = v) ⇒ P);

//symbol BOOL22 [v : El exp] [H : El (list prd)] [P : El prd] :
//  ✓ (H ⟝ (v = FALSE) ⇒ P) →
//  ✓ (H ⟝ (FALSE = v) ⇒ P);

//symbol BOOL31 [v : El exp] [H : El (list prd)] [P : El prd] :
//  ✓ (H ⟝ (v = FALSE) ⇒ P) →
//  ✓ (H ⟝ ¬ (v = TRUE) ⇒ P);

//symbol BOOL32 [v : El exp] [H : El (list prd)] [P : El prd] :
//  ✓ (H ⟝ (v = TRUE) ⇒ P) →
//  ✓ (H ⟝ ¬ (v = FALSE) ⇒ P);

//symbol BOOL41 [v : El exp] [H : El (list prd)] [P : El prd] :
//  ✓ (H ⟝ (v = FALSE) ⇒ P) →
//  ✓ (H ⟝ ¬ (TRUE = v) ⇒ P);

//symbol BOOL42 [v : El exp] [H : El (list prd)] [P : El prd] :
//  ✓ (H ⟝ (v = TRUE) ⇒ P) →
//  ✓ (H ⟝ ¬ (FALSE = v) ⇒ P);

//symbol BOOL51 [H : El (list prd)] [P : El prd] :
//  ✓ (H ⟝ (TRUE = FALSE) ⇒ P);

//symbol BOOL52 [H : El (list prd)] [P : El prd] :
//  ✓ (H ⟝ (FALSE = TRUE) ⇒ P);



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
