// B.lp — Foundation (shallow encoding)
// Predicates are Prop, expressions are τ ι.
// ι is the universal domain of B-method set theory.
// Connectives come from Stdlib.
require open
  Stdlib.Set Stdlib.Prop Stdlib.Bool
  Stdlib.Classic Stdlib.PropExt
  Stdlib.Eq Stdlib.String
  Stdlib.FOL Stdlib.HOL
  Stdlib.Impred
  Stdlib.List Stdlib.Nat
  Stdlib.Conj Stdlib.Disj;

// ---- Trusted arithmetic oracle ----
// Used to fill computable arithmetic facts (solver-confirmed)
// that we cannot yet prove from axioms.
opaque symbol trust [P : Prop] : π P ≔ begin admit end;

// ---- Domain constants ----

// Inhabitedness (the B-universe is nonempty)
constant symbol inh : τ ι;

// Pairs (maplet)
constant symbol ↦ : τ ι → τ ι → τ ι;
notation ↦ infix right 6;

// Set membership
constant symbol ϵ : τ ι → τ ι → Prop;
notation ϵ infix 5;

// Booleans (as elements of ι)
constant symbol BTRUE : τ ι;
constant symbol BFALSE : τ ι;

// ---- Domain axioms ----

// Boolean set and axioms
constant symbol BOOL : τ ι;
symbol bool_cases (v : τ ι) :
  π (v ϵ BOOL) → π (v = BTRUE ∨ v = BFALSE);
symbol bool_distinct : π (BTRUE ≠ BFALSE);

// Pair injectivity
symbol pair_inj (a b c d : τ ι) :
  π ((a ↦ b) = (c ↦ d)) → π (a = c ∧ b = d);
symbol pair_cong (a b c d : τ ι) :
  π (a = c) → π (b = d) → π ((a ↦ b) = (c ↦ d));

// Set extensionality
symbol set_ext (A B : τ ι) :
  π ((A = B) ⇔ (`∀ x : τ ι, ((x ϵ A) ⇔ (x ϵ B))));

// ---- Arithmetic on τ ι ----
// Modeled after Stdlib.Z but on the universal domain τ ι.

symbol NAT : τ ι;

// Constants
constant symbol 𝟎 : τ ι;
constant symbol 𝟏 : τ ι;

// Operations
constant symbol + : τ ι → τ ι → τ ι;
notation + infix left 6;

constant symbol — : τ ι → τ ι; // unary minus
notation — prefix 7;

symbol - (x y : τ ι) ≔ x + (— y);
notation - infix left 6;

// Ordering
constant symbol ≤ : τ ι → τ ι → Prop;
notation ≤ infix 5;

symbol > ≔ λ x y, ¬ (x ≤ y);

constant symbol ≪ : τ ι → τ ι → Prop; // strict <
notation ≪ infix 5;



// Axioms
symbol leq_refl (x : τ ι) : π (x ≤ x);
symbol leq_antisym (x y : τ ι) :
  π (x ≤ y) → π (y ≤ x) → π (x = y);
symbol strict_to_leq (x y : τ ι) :
  π (x ≪ y) → π (x ≤ y);

// ---- Function application ----
// eapp f x is the B-method functional application f(x).
constant symbol eapp : τ ι → τ ι → τ ι;

// Set operations (for set translator)
constant symbol set_image : τ ι;
constant symbol inter : τ ι;
constant symbol union : τ ι;

// ---- PP normalisation quantifiers ----
// ♢ and ♡ are both semantically ∀, distinguished in PP
// for proof search heuristics only.
symbol ♢ [a] : (τ a → Prop) → Prop;
notation ♢ quantifier;
rule ♢ $f ↪ ∀ $f;

symbol ♡ [a] : (τ a → Prop) → Prop;
notation ♡ quantifier;
rule ♡ $f ↪ ∀ $f;
