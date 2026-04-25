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
  Stdlib.List Stdlib.Nat;

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

// Operations. Precedence chosen so `+/−` bind tighter than
// `≤/=`, matching Stdlib.Nat/Stdlib.Z.
constant symbol + : τ ι → τ ι → τ ι;
notation + infix left 20;

constant symbol — : τ ι → τ ι; // unary minus
notation — prefix 25;

symbol - (x y : τ ι) ≔ x + (— y);
notation - infix left 20;

// Ordering
constant symbol ≤ : τ ι → τ ι → Prop;
notation ≤ infix 5;

symbol > ≔ λ x y, ¬ (x ≤ y);
notation > infix 5;

// ≪ is a PP-internal proof-search marker (prevents AR12 loops); semantically
// identical to ≤. PP never emits ≪ on the wire, so we alias it here so that
// rule signatures retaining ≪ (AR5–AR8, AR13) unify with PP's ≤ hypotheses.
symbol ≪ : τ ι → τ ι → Prop ≔ ≤;
notation ≪ infix 5;

// Axioms — discretely ordered abelian group on τ ι.
// (Just enough to prove the §A.14 arithmetic rules; not a full
// formalisation of ℤ.)

// Order: reflexive, antisymmetric, transitive
symbol leq_refl (x : τ ι) : π (x ≤ x);
symbol leq_antisym (x y : τ ι) :
  π (x ≤ y) → π (y ≤ x) → π (x = y);
symbol leq_trans (x y z : τ ι) :
  π (x ≤ y) → π (y ≤ z) → π (x ≤ z);

// Additive abelian group: + is commutative, associative, with
// identity 𝟎 and inverse —. (— x and add_zero pinned only on
// the right; the left versions follow from add_comm.)
symbol add_comm (x y : τ ι) : π (x + y = y + x);
symbol add_assoc (x y z : τ ι) : π ((x + y) + z = x + (y + z));
symbol add_zero (x : τ ι) : π (x + 𝟎 = x);
symbol add_neg (x : τ ι) : π (x + — x = 𝟎);

// Translation invariance: x ≤ y → z + x ≤ z + y
symbol add_leq_l (x y z : τ ι) : π (x ≤ y) → π (z + x ≤ z + y);

// Discreteness around 0/1: 𝟏 is strictly positive, and there is
// no integer strictly between 𝟎 and 𝟏.
symbol one_not_leq_zero : π (¬ (𝟏 ≤ 𝟎));
symbol discrete (x : τ ι) : π (¬ (x ≤ 𝟎)) → π (𝟏 ≤ x);

// ---- Derived lemmas (left-/right- variants of the axioms) ----

opaque symbol zero_add (x : τ ι) : π (𝟎 + x = x) ≔
begin
  assume x; rewrite add_comm 𝟎 x; refine add_zero x
end;

opaque symbol neg_add (x : τ ι) : π ((— x) + x = 𝟎) ≔
begin
  assume x; rewrite add_comm (— x) x; refine add_neg x
end;

opaque symbol add_leq_r (x y z : τ ι) :
  π (x ≤ y) → π (x + z ≤ y + z) ≔
begin
  assume x y z h;
  rewrite add_comm x z;
  rewrite add_comm y z;
  refine add_leq_l x y z h
end;

// Sum of two non-positives is non-positive.
opaque symbol add_leq_zero (x y : τ ι) :
  π (x ≤ 𝟎) → π (y ≤ 𝟎) → π (x + y ≤ 𝟎) ≔
begin
  assume x y hx hy;
  refine leq_trans (x + y) (𝟎 + y) 𝟎 _ _
  { refine add_leq_r x 𝟎 y hx }
  { rewrite zero_add y; refine hy }
end;

// x ≤ y ↔ x − y ≤ 𝟎 (sub_leq is the forward direction; leq_of_sub
// is the converse). Used by AR3, AR5–AR8, AR13.
opaque symbol sub_leq (x y : τ ι) :
  π (x ≤ y) → π (x - y ≤ 𝟎) ≔
begin
  assume x y h;
  // x − y ≡ x + (—y); want x + (—y) ≤ 𝟎.
  // From x ≤ y, add_leq_r with z := (—y): x + (—y) ≤ y + (—y) = 𝟎.
  refine leq_trans (x + (— y)) (y + (— y)) 𝟎 _ _
  { refine add_leq_r x y (— y) h }
  { rewrite add_neg y; refine leq_refl 𝟎 }
end;

opaque symbol leq_of_sub (x y : τ ι) :
  π (x - y ≤ 𝟎) → π (x ≤ y) ≔
begin
  assume x y h;
  // Add y to both sides of (x + (—y)) ≤ 𝟎, then simplify.
  have h1 : π ((x + (— y)) + y ≤ 𝟎 + y) { refine add_leq_r (x + (— y)) 𝟎 y h };
  have eq1 : π ((x + (— y)) + y = x) {
    rewrite add_assoc x (— y) y;
    rewrite neg_add y;
    refine add_zero x
  };
  have h2 : π (x ≤ 𝟎 + y) { rewrite left eq1; refine h1 };
  rewrite left zero_add y; refine h2
end;

// — flips ≤. Used by AR5, AR6.
opaque symbol neg_leq_zero (a : τ ι) :
  π (— a ≤ 𝟎) → π (𝟎 ≤ a) ≔
begin
  assume a h;
  refine leq_of_sub 𝟎 a _;
  simplify;
  rewrite zero_add (— a); refine h
end;

// ---- Algebraic identities (group law consequences) ----

// Left cancellation: a + b = a + c ⊢ b = c.
opaque symbol add_left_cancel (a b c : τ ι) :
  π (a + b = a + c) → π (b = c) ≔
begin
  assume a b c h;
  rewrite left zero_add b;
  rewrite left neg_add a;
  rewrite add_assoc (— a) a b;
  rewrite h;
  rewrite left add_assoc (— a) a c;
  rewrite neg_add a;
  refine zero_add c
end;

// — is involutive: —(—x) = x.
opaque symbol neg_neg (x : τ ι) : π (— (— x) = x) ≔
begin
  assume x;
  refine add_left_cancel (— x) (— (— x)) x _;
  rewrite add_neg (— x);
  symmetry;
  refine neg_add x
end;

// Negation distributes over +: —(x + y) = (—x) + (—y).
opaque symbol opp_add (x y : τ ι) : π (— (x + y) = (— x) + (— y)) ≔
begin
  assume x y;
  refine add_left_cancel (x + y) (— (x + y)) ((— x) + (— y)) _;
  rewrite add_neg (x + y);
  // Goal: 𝟎 = (x + y) + ((— x) + (— y))
  symmetry;
  // Goal: (x + y) + ((— x) + (— y)) = 𝟎
  rewrite add_assoc x y ((— x) + (— y));
  // Goal: x + (y + ((— x) + (— y))) = 𝟎
  rewrite left add_assoc y (— x) (— y);
  // Goal: x + ((y + (— x)) + (— y)) = 𝟎
  rewrite add_comm y (— x);
  // Goal: x + (((— x) + y) + (— y)) = 𝟎
  rewrite add_assoc (— x) y (— y);
  // Goal: x + ((— x) + (y + (— y))) = 𝟎
  rewrite add_neg y;
  // Goal: x + ((— x) + 𝟎) = 𝟎
  rewrite add_zero (— x);
  // Goal: x + (— x) = 𝟎
  refine add_neg x
end;

// Sub-sub: x − (x − y) = y. The key normalisation lemma for AR3 + solver.
opaque symbol sub_sub (x y : τ ι) : π (x - (x - y) = y) ≔
begin
  assume x y;
  // x − (x − y) = x + —(x + (—y)) = x + ((—x) + (—(—y))) = x + ((—x) + y)
  //            = (x + (—x)) + y = 𝟎 + y = y.
  simplify;
  rewrite opp_add x (— y);
  rewrite neg_neg y;
  rewrite left add_assoc x (— x) y;
  rewrite add_neg x;
  refine zero_add y
end;

// ---- Function application ----
// eapp f x is the B-method functional application f(x).
constant symbol eapp : τ ι → τ ι → τ ι;

// Set operations (for set translator)
constant symbol set_image : τ ι;
constant symbol inter : τ ι;
constant symbol union : τ ι;
constant symbol FIN : τ ι;
constant symbol card : τ ι;

// ---- PP normalisation quantifiers ----
// ♢ and ♡ are both semantically ∀, distinguished in PP
// for proof search heuristics only.
symbol ♢ [a] : (τ a → Prop) → Prop;
notation ♢ quantifier;
rule ♢ $f ↪ ∀ $f;

symbol ♡ [a] : (τ a → Prop) → Prop;
notation ♡ quantifier;
rule ♡ $f ↪ ∀ $f;
