// B.lp — B-Book core (shallow encoding): membership, pairs, BOOL, set/relation
// operators.  Predicates are Prop, expressions are τ ι; ι is the universal
// domain.  Integer arithmetic lives in Int.lp (the sole Stdlib.Z client); the
// `Stdlib.Nat` open here is what supplies ℕ (Tuple arities) to downstream modules.
require open
  Stdlib.Set Stdlib.Prop Stdlib.Bool
  Stdlib.Classic Stdlib.PropExt
  Stdlib.Eq Stdlib.String
  Stdlib.FOL Stdlib.HOL
  Stdlib.Impred
  Stdlib.List Stdlib.Nat
  Stdlib.Tactic;

// ---- Domain constants ----
// Inhabitedness comes from Stdlib.Set's `el : Π a, τ a` ("sets are
// non-empty") — `el ι : τ ι`; no separate postulate needed.

// Pairs (maplet)
constant symbol ↦ : τ ι → τ ι → τ ι;
notation ↦ infix right 6;

// Set membership
constant symbol ϵ : τ ι → τ ι → Prop;
notation ϵ infix 5;

// Booleans embedded from Stdlib.Bool.  `from_bool` injects 𝔹 into the domain;
// `to_bool` is a left inverse (only the two boolean points matter), which makes
// the injectivity behind `bool_distinct` provable instead of postulated.
symbol from_bool : 𝔹 → τ ι;
symbol to_bool : τ ι → τ bool;
rule to_bool (from_bool $b) ↪ $b;

symbol BTRUE  ≔ from_bool true;
symbol BFALSE ≔ from_bool false;

// ---- Domain axioms ----

// BTRUE ≠ BFALSE: 𝔹's constructor disjointness (Stdlib `true≠false`) transported
// through the left inverse — proved, not postulated.
opaque symbol bool_distinct : π (BTRUE ≠ BFALSE) ≔
begin assume h; refine true≠false (feq to_bool h) end;

// BOOL is the *range* of from_bool.  Membership of the abstract `ϵ` against it is
// the one irreducible boolean axiom; the three facts PP uses are derived from it.
constant symbol BOOL : τ ι;
symbol bool_mem (v : τ ι) : π ((v ϵ BOOL) ⇔ (`∃ b, v = from_bool b));

opaque symbol bool_cases (v : τ ι) :
  π (v ϵ BOOL) → π (v = BTRUE ∨ v = BFALSE) ≔
begin
  assume v hv;
  refine ∃ₑ (∧ₑ₁ (bool_mem v) hv) (λ b hb, _);
  rewrite hb;
  refine ∨ₑ (case_𝔹 b) (λ ht, _) (λ hf, _)
  { rewrite ht; refine ∨ᵢ₁ (eq_refl BTRUE) }
  { rewrite hf; refine ∨ᵢ₂ (eq_refl BFALSE) }
end;

opaque symbol btrue_in_bool : π (BTRUE ϵ BOOL) ≔
begin refine ∧ₑ₂ (bool_mem BTRUE) (∃ᵢ true (eq_refl BTRUE)) end;

opaque symbol bfalse_in_bool : π (BFALSE ϵ BOOL) ≔
begin refine ∧ₑ₂ (bool_mem BFALSE) (∃ᵢ false (eq_refl BFALSE)) end;


// Pair injectivity
symbol pair_inj (a b c d : τ ι) :
  π ((a ↦ b) = (c ↦ d)) → π (a = c ∧ b = d);
symbol pair_cong (a b c d : τ ι) :
  π (a = c) → π (b = d) → π ((a ↦ b) = (c ↦ d));

// Set extensionality
symbol set_ext (A B : τ ι) :
  π ((A = B) ⇔ (`∀ x : τ ι, ((x ϵ A) ⇔ (x ϵ B))));


// ---- Function application ----
// eapp f x is the B-method functional application f(x).
constant symbol eapp : τ ι → τ ι → τ ι;

// Set-theoretic operators.  These are higher-order symbols of the encoding
// (NOT B-functions / sets of pairs), so they carry their real arrow types and
// are applied DIRECTLY — `eapp` is reserved for B-function application (App /
// EApp).  Uninterpreted: proofs never compute on them.
constant symbol set_image : τ ι → τ ι → τ ι;    // r[s]   relational image
constant symbol inter : τ ι → τ ι → τ ι;        // s /\ t
constant symbol union : τ ι → τ ι → τ ι;        // s \/ t
constant symbol interval : τ ι → τ ι → τ ι;     // a..b   (apero / EGALITE)
constant symbol inverse : τ ι → τ ι;            // r~     relational inverse
constant symbol dom_restrict : τ ι → τ ι → τ ι; // s <| r domain restriction
constant symbol ran_restrict : τ ι → τ ι → τ ι; // r |> t range restriction
constant symbol set_cons : τ ι → τ ι → τ ι;     // {a, …} extension cell
constant symbol set_empty : τ ι;                // {}     empty set
constant symbol total_func : τ ι → τ ι → τ ι;   // s --> t total functions
constant symbol overriding : τ ι → τ ι → τ ι;   // r <+ s relational override
constant symbol relcomp : τ ι → τ ι → τ ι;      // r ; s  relational composition
constant symbol prod : τ ι → τ ι → τ ι;         // s * t  product (set ×, or ·)
constant symbol power : τ ι → τ ι → τ ι;        // a ** b exponentiation
constant symbol subset : τ ι → τ ι → Prop;      // s <: t
constant symbol lt : τ ι → τ ι → Prop;          // a < t  strict less-than
constant symbol bool_of : Prop → τ ι;           // bool(P) predicate→BOOL element

// B built-in set/relation operators.  Like the operators above, these are
// "too big" to be object-level B-functions (sets of pairs): they are applied
// DIRECTLY, NOT via `eapp` (see Syntax_pp.meta_ops).  All unary except `func`.
constant symbol card : τ ι → τ ι;        // card(s)   cardinality
constant symbol dom : τ ι → τ ι;         // dom(r)    domain
constant symbol ran : τ ι → τ ι;         // ran(r)    range
constant symbol perm : τ ι → τ ι;        // perm(s)   permutations
constant symbol iseq : τ ι → τ ι;        // iseq(s)   injective sequences
constant symbol seq : τ ι → τ ι;         // seq(s)    sequences
constant symbol seq1 : τ ι → τ ι;        // seq1(s)   non-empty sequences
constant symbol POW : τ ι → τ ι;         // POW(s)    powerset
constant symbol POW1 : τ ι → τ ι;        // POW1(s)   non-empty powerset
constant symbol FIN : τ ι → τ ι;         // FIN(s)    finite subsets
constant symbol FIN1 : τ ι → τ ι;        // FIN1(s)   non-empty finite subsets
constant symbol id : τ ι → τ ι;          // id(s)     identity relation
constant symbol sz : τ ι → τ ι;          // _sz(s)    size
constant symbol func : τ ι → τ ι → τ ι → τ ι;  // _func(…)  function builder

// Pair projections: PP's `_pj1(p)` / `_pj2(p)` (the components of a pair
// `p`), applied via `eapp` (object-level — they project an actual pair).
// Uninterpreted — proofs use them syntactically, never computing on them.
constant symbol pj1 : τ ι;
constant symbol pj2 : τ ι;

// ---- PP normalisation quantifiers ----
// The n-ary ♢ / ♡ live in Quant.lp (tuple-based, alongside `!!` / `??`).
