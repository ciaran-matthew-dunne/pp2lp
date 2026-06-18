// B.lp — the trusted base of the shallow B encoding.
//
// Postulated only: constant symbols, axioms, definitions, and the rewrite rules
// that drive reduction. Proved lemmas live in lemmas/; per-section proof rules
// in rules/.
//
// Predicates are Prop; expressions are τ ι (ι the universal domain). The surface
// is ℤ-global: Stdlib.Z is opened last, so bare decimals are ℤ. ℕ-indexed
// positions (Tuple/prj arities) coerce via to_nat (end of the integer section).
require open
  Stdlib.Set Stdlib.Prop Stdlib.Bool
  Stdlib.Classic Stdlib.PropExt
  Stdlib.Eq Stdlib.FOL Stdlib.Impred Stdlib.Z;


// ---- set membership ----
constant symbol ϵ : τ ι → τ ι → τ o;
notation ϵ infix 5;

// extensionality
symbol set_ext (A B : τ ι) :
  π ((A = B) ⇔ (`∀ x : τ ι, ((x ϵ A) ⇔ (x ϵ B))));

// ---- ordered pairs (maplet) ----
constant symbol ↦ : τ ι → τ ι → τ ι;
notation ↦ infix right 6;

// injectivity + congruence of pairing (TODO: provable?)
symbol pair_inj (a b c d : τ ι) :
  π ((a ↦ b) = (c ↦ d)) → π (a = c ∧ b = d);
symbol pair_cong (a b c d : τ ι) :
  π (a = c) → π (b = d) → π ((a ↦ b) = (c ↦ d));

// ---- domain-level booleans ----
// from_bool injects 𝔹 into the domain; to_bool is its left inverse.
symbol from_bool : τ bool → τ ι;
symbol to_bool : τ ι → τ bool;
rule to_bool (from_bool $b) ↪ $b;

// BOOL is the range of from_bool.
constant symbol BOOL : τ ι;
symbol bool_mem (v : τ ι) : π ((v ϵ BOOL) ⇔ (`∃ b, v = from_bool b));

symbol BTRUE  ≔ from_bool true;
symbol BFALSE ≔ from_bool false;


// ======================================================================
// Tuples — the carrier of n-ary quantification
// ======================================================================

inductive Tuple : ℕ → TYPE ≔
  | unit : Tuple _0
  | ⨾ [n] : Tuple n → τ ι → Tuple (+1 n);
notation ⨾ infix left 5;


// k-th projection; prj 0 is the rightmost (most recently appended) element.
symbol prj [n] (k : ℕ) (_ : Tuple n) : τ ι;
rule prj (+1 $n) ($t ⨾ _) ↪ prj $n $t
with prj _0       (_ ⨾ $x) ↪ $x;

// Canonical inhabitant of Tuple n (every slot el ι), for rules needing a witness
// tuple whose predicate ignores the contents.
symbol inh_tuple [n] : Tuple n;
rule inh_tuple [_0] ↪ unit
with inh_tuple [+1 $n] ↪ inh_tuple [$n] ⨾ el ι;

// ---- Tuple split: ++, take, drop ----
// Left-recursive ℕ addition (unlike Stdlib.Nat.+, which reduces on the right):
// `Tuple ((+1 n) ++ m)` reduces to `Tuple (+1 (n ++ m))`, so its inhabitants are
// visibly tuple constructors.
symbol ++ : ℕ → ℕ → ℕ; notation ++ infix 5;
rule _0 ++ $m ↪ $m
with +1 $n ++ $m ↪ +1 ($n ++ $m);

// take/drop split a (n+m)-tuple: take keeps the leftmost n, drop the rightmost m.
// Indices stay explicit so call sites name them and the rules fire (avoids needing
// `(n+m)-n = m` definitionally, which fails for abstract n, m).
symbol take [n m] (v : Tuple (n ++ m)) : Tuple n;
symbol drop [n m] (v : Tuple (n ++ m)) : Tuple m;
rule drop [_0]      [_]  $v        ↪ $v
with drop [+1 $n] [$m] ($v ⨾ _)   ↪ drop [$n] [$m] $v
with take [_0]      [_]  _         ↪ unit
with take [+1 $n] [$m] ($v ⨾ $x)  ↪ take [$n] [$m] $v ⨾ $x;

// prj commutes through take/drop on an abstract v (the rules above only fire on a
// concrete `_ ⨾ _`): take keeps low indices, drop shifts the kept ones up by n.
rule prj $k (take [$n] [$m] $v) ↪ prj $k $v
with prj $k (drop [$n] [$m] $v) ↪ prj ($n ++ $k) $v;

// ---- Tuple value destructor + η ----
// Set-code for Tuple (mirrors list* for 𝕃*), so the polymorphic `=` (over τ a)
// reaches tuple values — otherwise inexpressible on `Tuple n : TYPE`.
symbol Tup : ℕ → Set;
rule τ (Tup $n) ↪ Tuple $n;

// init v: all but the last (prj 0) element.
symbol init [n] : Tuple (+1 n) → Tuple n;
rule init ($v ⨾ _) ↪ $v;

// prj through init on an abstract tuple: drops slot 0, shifts the rest down.
rule prj $k (init $v) ↪ prj (+1 $k) $v;

// ---- Slot surgery: rm1/rm2, tuple_insert1/2, tuple_prepend ----
// NRM20/21 may pin (NRM26 may drop) the binder at slot 1 or 2, not just slot 0
// (init/⨾) or the leftmost (tuple_prepend). rmK removes slot K, tuple_insertK
// inserts there; the prj-commute rules keep projections reducible on abstract v.
symbol rm1 [n] : Tuple (+1 (+1 n)) → Tuple (+1 n);
rule rm1 ($v ⨾ $y) ↪ (init $v) ⨾ $y;
rule prj _0 (rm1 $v) ↪ prj _0 $v
with prj (+1 $k) (rm1 $v) ↪ prj (+1 (+1 $k)) $v;

symbol tuple_insert1 [n] : τ ι → Tuple (+1 n) → Tuple (+1 (+1 n));
rule tuple_insert1 $x ($v ⨾ $y) ↪ ($v ⨾ $x) ⨾ $y;
// NB: a bare numeral ≥1 in a rule pattern is a wildcard — spell slot 1 `+1 _0`.
rule prj _0 (tuple_insert1 _ $w) ↪ prj _0 $w
with prj (+1 _0) (tuple_insert1 $x _) ↪ $x
with prj (+1 (+1 $k)) (tuple_insert1 _ $w) ↪ prj (+1 $k) $w
with rm1 (tuple_insert1 _ $w) ↪ $w;

symbol rm2 [n] : Tuple (+1 (+1 (+1 n))) → Tuple (+1 (+1 n));
rule rm2 ($v ⨾ $y) ↪ (rm1 $v) ⨾ $y;
rule prj _0 (rm2 $v) ↪ prj _0 $v
with prj (+1 _0) (rm2 $v) ↪ prj (+1 _0) $v
with prj (+1 (+1 $k)) (rm2 $v) ↪ prj (+1 (+1 (+1 $k))) $v;

symbol tuple_insert2 [n] : τ ι → Tuple (+1 (+1 n)) → Tuple (+1 (+1 (+1 n)));
rule tuple_insert2 $x ($v ⨾ $y) ↪ (tuple_insert1 $x $v) ⨾ $y;
rule prj _0 (tuple_insert2 _ $w) ↪ prj _0 $w
with prj (+1 _0) (tuple_insert2 _ $w) ↪ prj (+1 _0) $w
with prj (+1 (+1 _0)) (tuple_insert2 $x _) ↪ $x
with prj (+1 (+1 (+1 $k))) (tuple_insert2 _ $w) ↪ prj (+1 (+1 $k)) $w
with rm2 (tuple_insert2 _ $w) ↪ $w;

// Prepend at the leftmost slot (the last-listed binder; historical NRM26 form).
// The k = 0 commute is sound (prepending never displaces the rightmost slot).
symbol tuple_prepend [n] : τ ι → Tuple n → Tuple (+1 n);
rule tuple_prepend [_0] $x unit ↪ unit ⨾ $x
with tuple_prepend [+1 $n] $x ($w ⨾ $y) ↪ tuple_prepend [$n] $x $w ⨾ $y;
rule prj _0 (tuple_prepend [+1 _] _ $v) ↪ prj _0 $v
with prj _0 (tuple_prepend [_0] $x _) ↪ $x;

// Motive for tuple η (proved as tuple_eta in lemmas/Tuple.lp): ⊤ at index 0, the
// η statement at a successor, so init/prj 0 apply only where well-typed.
symbol eta_motive : Π m, Tuple m → Prop;
rule eta_motive _0      _   ↪ ⊤
with eta_motive (+1 _) $v  ↪ ((init $v) ⨾ (prj _0 $v)) = $v;


// ======================================================================
// n-ary quantifiers — !! / ?? (and the PP markers ♢ / ♡)
// ======================================================================
// Kept rigid (no reduction rules): eager reduction to nested ∀ would erase the
// surface form before tactics see it, and inferring n/P at call sites would need
// to invert the reduction (HO-unification), which Lambdapi can't. The Π bridges
// are axiomatised here; the _cong/_const lemmas are in lemmas/Tuple.lp.

constant symbol !! [n] : (Tuple n → Prop) → Prop;
notation !! quantifier;

constant symbol pi_to_!! [n] (P : Tuple n → Prop)
  : (Π v : Tuple n, π (P v)) → π (`!! v, P v);

constant symbol !!_to_pi [n] (P : Tuple n → Prop)
  : π (`!! v, P v) → Π v : Tuple n, π (P v);

constant symbol ?? [n] : (Tuple n → Prop) → Prop;
notation ?? quantifier;

constant symbol pi_to_??_intro [n] (P : Tuple n → Prop)
  : Π v : Tuple n, π (P v) → π (`?? v, P v);

constant symbol pi_to_??_elim [n] (P : Tuple n → Prop) [R : Prop]
  : (Π v : Tuple n, π (P v) → π R) → π (`?? v, P v) → π R;

// ♢ (goal-side) / ♡ (hypothesis-side) n-ary universals: both are `!!`, carrying
// only a proof-search role. Rigid like !!; the equalities to !! (♢_eq_!!/♡_eq_!!)
// are proved in lemmas/Tuple.lp.
symbol ♢ [n] : (Tuple n → Prop) → Prop ≔ !!;
notation ♢ quantifier;

constant symbol pi_to_♢ [n] (P : Tuple n → Prop)
  : (Π v : Tuple n, π (P v)) → π (`♢ v, P v);

constant symbol ♢_to_pi [n] (P : Tuple n → Prop)
  : π (`♢ v, P v) → Π v : Tuple n, π (P v);

symbol ♡ [n] : (Tuple n → Prop) → Prop ≔ !!;
notation ♡ quantifier;

constant symbol pi_to_♡ [n] (P : Tuple n → Prop)
  : (Π v : Tuple n, π (P v)) → π (`♡ v, P v);

constant symbol ♡_to_pi [n] (P : Tuple n → Prop)
  : π (`♡ v, P v) → Π v : Tuple n, π (P v);


// ======================================================================
// Function application + set/relation operators
// ======================================================================

// B-method application f(x).
constant symbol eapp : τ ι → τ ι → τ ι;

// Set-builder / aggregate binders %(xs).(P | E) and SIGMA(xs).(P | E).
// Uninterpreted: predicate and value are Tuple n-indexed, so they type-check
// without a committed semantics.
constant symbol set_lambda [n] : (Tuple n → Prop) → (Tuple n → τ ι) → τ ι;
constant symbol sigma [n] : (Tuple n → Prop) → (Tuple n → τ ι) → τ ι;

// Higher-order operators of the encoding (NOT sets of pairs): real arrow types,
// applied directly (not via eapp). Uninterpreted — proofs never compute on them.
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

// B built-in set/relation operators (also applied directly, not via eapp).
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


// ======================================================================
// Integers — embedded from Stdlib.Z
// ======================================================================
// from_int : ℤ → τ ι injects ℤ; to_int is its left inverse, INT its range.
// plus/neg/leq (with 𝟎/𝟏, minus, gt) are abstract — rigid under conversion —
// and bridged to ℤ by the def-axioms plus_def/neg_def/le_def. The group laws are
// proved from these in lemmas/Int.lp.
symbol NAT : τ ι;

injective symbol from_int : ℤ → τ ι;
injective symbol to_int : τ ι → τ int;
rule to_int (from_int $z) ↪ $z;

constant symbol INT : τ ι;
symbol int_mem (v : τ ι) : π ((v ϵ INT) ⇔ (`∃ z, v = from_int z));

symbol 𝟎 ≔ from_int 0;
symbol 𝟏 ≔ from_int 1;

// plus/neg kept abstract (like leq): rigid under conversion, so they never unfold
// into the from_int/to_int embedding and unification on a rule conclusion recovers
// their operands. plus_def/neg_def give their meaning propositionally. injective
// recovers operands for an implicit `plus ?E ?F` against a concrete goal (AR4 etc.).
injective symbol plus : τ ι → τ ι → τ ι;
symbol plus_def (x y : τ ι) : π (plus x y = from_int (to_int x + to_int y));

injective symbol neg : τ ι → τ ι; // unary minus
symbol neg_def (x : τ ι) : π (neg x = from_int (— (to_int x)));

// `to_int` projects plus/neg onto Stdlib.Z by REDUCTION — the to_int-image of
// plus_def/neg_def composed with the retract (`to_int (from_int z) ↪ z`), so a
// conservative orientation of those axioms (sound by to_int's injectivity). This
// makes ground arithmetic *compute* (`to_int (plus (from_int 2) (from_int 3)) ↪
// 2 + 3 ↪ 5`) and lets the emitter prove arithmetic reorderings on ℤ. `plus`/`neg`
// stay rigid (no rule fires on a bare `plus x y`), so unification still recovers
// operands.
rule to_int (plus $x $y) ↪ to_int $x + to_int $y
with to_int (neg $x)     ↪ — (to_int $x);

symbol minus (x y : τ ι) ≔ plus x (neg y);

// Decimal literals: a numeral parses as ℤ and coerces into τ ι via from_int, so
// the emitter can write bare numerals where a τ ι is expected.
coerce_rule coerce ℤ (τ ι) $z ↪ from_int $z;
coerce_rule coerce (τ ι) ℤ $z ↪ to_int $z;
// leq abstract for the same reason: reducing through Z's ≤ would lose the operands
// (fatal for reflexive `leq E E`, where to_int ?E ≐ to_int ?E erases ?E). le_def is
// its meaning; le_intro/le_elim (lemmas/Int.lp) bridge to Stdlib.Z.≤.
injective symbol leq : τ ι → τ ι → Prop;

symbol le_def (x y : τ ι) : π (leq x y = (to_int x ≤ to_int y));

symbol gt ≔ λ x y, ¬ (leq x y);

// ≪ : a PP-internal proof-search marker (blocks AR12 loops), semantically leq. PP
// never emits ≪, so we alias it for the rule signatures that retain it (AR5–8, AR13).
symbol ≪ : τ ι → τ ι → Prop ≔ leq;
notation ≪ infix 5;

// card is integer-valued (B typing card : FIN(s) → ℕ ⊆ INT), so card(s) discharges
// its `ϵ INT` side-condition. A typing postulate, like the operators themselves.
symbol card_in_int (s : τ ι) : π (card s ϵ INT);

// ---- ℤ → ℕ surface bridge ----
// The surface is ℤ-global, so a literal Tuple/prj index parses as ℤ; to_nat bridges
// it to ℕ and computes (`to_nat (Zpos p) ↪ val p`), so `Tuple (to_nat 3) ≡ Tuple 3`
// and the rule library is used unchanged.
symbol to_nat : ℤ → ℕ;
rule to_nat Z0 ↪ _0
with to_nat (Zpos $p) ↪ val $p;

coerce_rule coerce ℤ ℕ $z ↪ to_nat $z;



// ======================================================================
// ⋀ — n-ary conjunction over snoc lists 𝕃*
// ======================================================================
// PP's ∧ is left-associative, so the last conjunct is the outer constructor of a
// snoc list, and PP's AND rules become a single match on `ps ∷ P`. A conjunction
// is always `⋀ <list>`, never a native ∧, so singleton/nil collapses never arise.
// The four eliminators below are the trusted axiomatisation.

// snoc list: grows on the right (∷), empty is ∎.
(a : Set) inductive 𝕃* : TYPE ≔
  | ∎ : 𝕃* a
  | ∷ : 𝕃* a → τ a → 𝕃* a;
notation ∷ infix left 5;

symbol list* : Set → Set;
rule τ (list* $a) ↪ 𝕃* $a;

symbol ite [a] : 𝔹 → τ a → τ a → τ a;
rule ite true $x _  ↪ $x
with ite false _ $y ↪ $y;

symbol is_nil [a] : 𝕃* a → 𝔹;
rule is_nil ∎       ↪ true
with is_nil (_ ∷ _) ↪ false;

// ⊤ elements are discharged conjuncts (PP drops them); result lists must too, or
// combined res_tm's diverge from PP's formulas. mk_0 keeps ⊤ out of leaf lists;
// the two ⊤-rules drop a ⊤ entering a combine. Sound (⊤ ∧ X ⟺ X). Sequential: the
// ⊤-rules must precede the general cons rule.
sequential symbol concat [a] : 𝕃* a → 𝕃* a → 𝕃* a;
rule concat $xs ∎ ↪ $xs
with concat ∎ $ys ↪ $ys
with concat ($xs ∷ ⊤) $ys ↪ concat $xs $ys
with concat $xs ($ys ∷ ⊤) ↪ concat $xs $ys
with concat $xs ($ys ∷ $y) ↪ (concat $xs $ys) ∷ $y;

symbol dropl [a] : 𝕃* a → 𝕃* a;
rule dropl ∎          ↪ ∎
with dropl ($xs ∷ $x) ↪ ite (is_nil $xs) ∎ ((dropl $xs) ∷ $x);

symbol popl [a] : 𝕃* a → τ a;
rule popl ($xs ∷ $x) ↪ ite (is_nil $xs) $x (popl $xs);

symbol pushl [a] : τ a → 𝕃* a → 𝕃* a;
rule pushl $x ∎ ↪ (∎ ∷ $x)
with pushl $x ($ys ∷ $y) ↪ (pushl $x $ys) ∷ $y;

injective symbol ⋀ : 𝕃* o → Prop;
notation ⋀ prefix 30;
rule ⋀ (∎ ∷ $p) ↪ $p
with ⋀ ($ps ∷ ⊤) ↪ ⋀ $ps;

// TODO: make non-sequential.
sequential symbol ⋀_snoc : Prop → Prop → Prop;
rule ⋀_snoc (⋀ $ps) $p ↪ ⋀ ($ps ∷ $p)
with ⋀_snoc $p $q ↪ ⋀ (∎ ∷ $p ∷ $q);

symbol conj : 𝕃* o → τ o;
rule conj ∎ ↪ ⊤
with conj ($p ∷ $q) ↪ ite (is_nil $p) ($q) (⋀ ($p ∷ $q));

injective symbol Res : τ o → TYPE;
symbol mk_res [t] (ts : 𝕃* o) : π (t = conj ts) → Res t;
symbol res_ts [t] (r : Res t) : 𝕃* o;
symbol res_eq [t] (r : Res t) : π (t = conj (res_ts r));
rule res_ts (mk_res $ts _)  ↪ $ts;
rule res_eq (mk_res _ $prf) ↪ $prf;

// Defined (not a rule) so `res_tm r ≡ conj (res_ts r)` holds for a variable r too.
symbol res_tm [t] (r : Res t) : τ o ≔ conj (res_ts r);

// Singleton result: `conj (∎ ∷ x) ≡ x`, so a leaf/passthrough proof `π (t = x)` fits.
symbol mk_1 [t] (x : τ o) (prf : π (t = x)) : Res t ≔ mk_res (∎ ∷ x) prf;

// Discharged result (t = ⊤): the empty list, which concat erases anywhere, so a
// combined res_tm keeps exactly PP's surviving conjuncts. `conj ∎ ↪ ⊤`.
symbol mk_0 [t] (prf : π (t = ⊤)) : Res t ≔ mk_res ∎ prf;

// Structural intro/eliminators (peel/grow the last conjunct); ⋀_nil_prf is the
// empty conjunction. Derived lemmas (⋀_push_front, ⋀_pop_intro, conj_*, ⋀₂_*) in
// lemmas/ConjList.lp.
symbol ⋀_nil_prf : π (⋀ ∎);
symbol ⋀_intro [ps : 𝕃* o] [P : Prop] : π (⋀ ps) → π P → π (⋀ (ps ∷ P));
symbol ⋀_init  [ps : 𝕃* o] [P : Prop] : π (⋀ (ps ∷ P)) → π (⋀ ps);
symbol ⋀_last  [ps : 𝕃* o] [P : Prop] : π (⋀ (ps ∷ P)) → π P;
