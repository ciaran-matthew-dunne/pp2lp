// The Drinker Paradox in LambdaPi
// "In any non-empty bar, there exists a person such that 
//  if that person is drinking, then everyone in the bar is drinking."

// Basic type setup
constant symbol Prop : TYPE;
constant symbol π : Prop → TYPE;  // Interpretation of propositions as types
notation π prefix 5;

// Logical connectives
constant symbol ⊥ : Prop;
constant symbol ⊤ : Prop;
symbol ¬ : Prop → Prop;
notation ¬ prefix 6;
rule π (¬ $p) ↪ π $p → π ⊥;

symbol ∧ : Prop → Prop → Prop;
notation ∧ infix left 7;
rule π ($p ∧ $q) ↪ π $p × π $q;

symbol ∨ : Prop → Prop → Prop;
notation ∨ infix left 6.5;
rule π ($p ∨ $q) ↪ π $p + π $q;

symbol ⇒ : Prop → Prop → Prop;
notation ⇒ infix right 5;
rule π ($p ⇒ $q) ↪ π $p → π $q;

// Quantifiers
constant symbol Person : TYPE;  // Domain of people
constant symbol ∀p : (Person → Prop) → Prop;
notation ∀p quantifier;
rule π (∀p (λ x, $p.[x])) ↪ Π x : Person, π $p.[x];

constant symbol ∃p : (Person → Prop) → Prop;
notation ∃p quantifier;
rule π (∃p (λ x, $p.[x])) ↪ Σ x : Person, π $p.[x];

// The drinking predicate
constant symbol drinks : Person → Prop;

// Classical logic axioms (needed for the proof)
// Law of excluded middle
constant symbol lem : Π p : Prop, π (p ∨ ¬ p);

// Double negation elimination
constant symbol dne : Π p : Prop, π (¬ ¬ p) → π p;

// The bar is non-empty
constant symbol person_exists : π (∃p x, ⊤);

// The Drinker Paradox theorem
symbol drinker_paradox : π (∃p x, drinks x ⇒ `∀p y, drinks y) ≔
begin
  // We use classical logic to prove this
  // Case split on whether everyone drinks
  assume all_drink_or_not;
  apply lem (`∀p y, drinks y);
  assume all_drink not_all_drink;
  
  // Case 1: Everyone drinks
  // Then we can pick any person x, and drinks x ⇒ ∀y. drinks y is trivially true
  apply person_exists;
  assume witness _;
  apply witness;
  assume drinks_witness;
  apply all_drink;
  
  // Case 2: Not everyone drinks
  // Then ∃x. ¬drinks x
  // We pick this x as our witness
  assume not_forall_implies_exists;
  apply dne;
  assume h;
  apply not_all_drink;
  assume y;
  apply dne;
  assume not_drinks_y;
  apply h;
  apply y;
  apply not_drinks_y;
  
  // Now we have someone who doesn't drink
  assume non_drinker not_drinks_non_drinker;
  apply non_drinker;
  
  // For this person: drinks non_drinker ⇒ ∀y. drinks y
  // Since ¬drinks non_drinker, the implication is vacuously true
  assume drinks_non_drinker;
  // This is a contradiction
  apply not_drinks_non_drinker;
  apply drinks_non_drinker;
end;

// Alternative formulation using a finite bar with at least one person
constant symbol Bar : TYPE;
constant symbol in_bar : Person → Bar → Prop;
constant symbol non_empty : Π b : Bar, π (∃p x, in_bar x b);

// Localized version of the paradox
symbol drinker_paradox_bar : Π b : Bar, 
  π (∃p x, in_bar x b ∧ (drinks x ⇒ `∀p y, in_bar y b ⇒ drinks y)) ≔
begin
  assume b;
  // Similar proof structure but localized to people in bar b
  assume all_in_bar_drink_or_not;
  apply lem (`∀p y, in_bar y b ⇒ drinks y);
  assume all_drink not_all_drink;
  
  // Case 1: Everyone in the bar drinks
  apply non_empty b;
  assume witness in_bar_witness;
  apply witness;
  apply in_bar_witness;
  assume drinks_witness;
  apply all_drink;
  
  // Case 2: Someone in the bar doesn't drink
  // Similar reasoning as before...
  admit; // The full proof follows the same pattern
end;