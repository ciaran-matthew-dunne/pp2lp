require open pp2lp.Prelude;

// ------ predicates, expressions, formulas ------
symbol 𝕊 : TYPE;      // define type for strings,
builtin "String" ≔ 𝕊; // bind string literals to this type.

symbol str : Set;     // called `idt` in the PP docs.
rule El str ↪ 𝕊;      //


// set-codes for basic syntactic categories.
symbol vrb : Set ≔ list str; // "variable binding"
symbol prd : Set; // "predicate"
symbol exp : Set; // "expression"
symbol idv : Set; // "individual" - special type we use for "constants".

assert [a : Set] ⊢ a : Set;

// 'lift' an expression to a predicate.
injective symbol Ψ : El exp → El prd;
coerce_rule coerce (El exp) (El prd) $p ↪ Ψ $p;

// 'lift' an individual to an expression.
injective symbol ι : El idv → El exp;
coerce_rule coerce (El idv) (El exp) $x ↪ ι $x;
coerce_rule coerce (El idv) (El prd) $x ↪ Ψ (ι $x);

// ----- primitive logical symbols --------------
// basic logical connectives.
injective symbol VRAI : El prd;
injective symbol FAUX : El prd;
injective symbol and  : El (prd ⤳ prd ⤳ prd);
injective symbol or   : El (prd ⤳ prd ⤳ prd);
injective symbol =>   : El (prd ⤳ prd ⤳ prd);


injective symbol <=>  : El (prd ⤳ prd ⤳ prd);
injective symbol not  : El (prd ⤳ prd);
injective symbol =    : El (exp ⤳ exp ⤳ prd);

notation =   infix left 2;
notation and infix left 2;
notation or  infix left 2;
notation =>  infix left 2;
notation <=> infix left 1;
notation not prefix 3;

// quantifiers. explicit variable lists! not HOAS!
injective symbol ! : El vrb → El prd → El prd; // aka. ∀
injective symbol # : El (vrb ⤳ prd ⤳ prd);    // aka. ∃
injective symbol ♢ : El (vrb ⤳ prd ⤳ prd);   // aka. forall
injective symbol ♡ : El (vrb ⤳ prd ⤳ prd);   // aka. forall2

// hacky notation for building string lists (e.g., for variable bindings).
symbol ⋅ : El (str ⤳ list str)        ≔ λ x, cons x nil;            // length 1
symbol ⨾ : El (str ⤳ str ⤳ list str) ≔ λ x y, cons x (cons y nil); // length 2

notation ⋅ postfix 10;
notation ⨾ infix right 5;

// set-theoretic membership.
injective symbol ∈ : El (exp ⤳ exp ⤳ prd);
notation ∈ infix left 2;

// set-theoretic equality. used only by `EQS1` and `EQS2`.
symbol eql_set : El (exp ⤳ exp ⤳ prd);

// ----- expressions -------------------------

// infix constructor for ordered pairs
symbol ∥ : El (exp ⤳ exp ⤳ exp);
notation ∥ infix left 5;

// cast strings to expressions.
injective symbol var : El (str ⤳ exp);
coerce_rule coerce 𝕊 (El exp) $str ↪ var $str;

// helper function for `vars`.
sequential symbol vars_aux : El (exp ⤳ vrb ⤳ exp);
rule vars_aux $e nil           ↪ $e
with vars_aux $e (cons $y $ys) ↪ vars_aux ($e ∥ var $y) $ys ;

// convert variable list to an expression.
symbol vars : El (vrb ⤳ exp);
rule vars (cons $x $xs) ↪ vars_aux (var $x) $xs;

// set-theoretic function/predicate application.
injective symbol ‵ : El (exp ⤳ exp ⤳ exp);
notation ‵ infix left 10;

// symbols for arithmetic.
injective symbol > : El (exp ⤳ exp ⤳ prd);
injective symbol ≤ : El (exp ⤳ exp ⤳ prd);
injective symbol < : El (exp ⤳ exp ⤳ prd);
injective symbol ≪ : El (exp ⤳ exp ⤳ prd);
injective symbol 𝟎 : El (exp);
injective symbol 𝟏 : El (exp);
injective symbol ⨪ : El (exp ⤳ exp);
injective symbol + : El (exp ⤳ exp ⤳ exp);
injective symbol - : El (exp ⤳ exp ⤳ exp);

notation > infix 5;
notation ≤ infix 5;
notation < infix 5;
notation ≪ infix 5;
notation + infix 5;
notation - infix 5;

// evaluation of 'atomic' arithmetic expressions.
symbol ev [a : Set] : El (a ⤳ bool);

// mysterious 'solveur' operation.
// only meaningful when `a ≡ exp` or `a ≡ prd`.
// ?? symbolic reduction of predicates/expressions with computable arithmetic ??
symbol solveur [a : Set] : El (a ⤳ a);
rule solveur (Ψ $e) ↪ Ψ (solveur $e);
rule solveur (ι $p) ↪ (ι $p);

// ----- Operations on terms -----------------------
// syntactic equality on expressions and predicates.
sequential symbol == [a : Set] : El (a ⤳ a ⤳ bool);
notation == infix 5;

// syntactic equality on `str`.
rule ((==) [str] $x $x) ↪ true
with ((==) [str] _  _)  ↪ false;

// syntactic equality on `prd`.
rule FAUX == FAUX ↪ true
with VRAI == VRAI ↪ true
with (not $p) == (not $q)           ↪ ($p == $q)
with ($p1 and $p2) == ($q1 and $q2) ↪ ($p1 == $q1) && ($p2 == $q2)
with ($p1 or $p2) == ($q1 or $q2)   ↪ ($p1 == $q1) && ($p2 == $q2)
with ($p1 => $p2) == ($q1 => $q2)   ↪ ($p1 == $q1) && ($p2 == $q2)
with ($p1 <=> $p2) == ($q1 <=> $q2) ↪ ($p1 == $q1) && ($p2 == $q2)
with ($e1 = $e2) == ($f1 = $f2)     ↪ ($e1 == $f1) && ($e2 == $f2)
with (Ψ $e1) == (Ψ $e2)             ↪ $e1 == $e2;
//with (! $P) == (! $Q) ↪ (`∀ x, ($P x == $Q x))
//with (# $P) == (# $Q) ↪ (`∀ x, ($P x == $Q x))
//with (♢ $P) == (♢ $Q) ↪ (`∀ x, ($P x == $Q x))
//with (♡ $P) == (♡ $Q) ↪ (`∀ x, ($P x == $Q x`));

// syntactic equality on `exp`.
rule (var $x == var $y) ↪ ($x == $y)
with ($e1 ‵ $e2) == ($f1 ‵ $f2) ↪ ($e1 == $f1) && ($e2 == $f2)
with (ι $p) == (ι $p) ↪ true;

// otherwise, return false.
rule _ == _ ↪ false;

symbol !== [a : Set] : El (a ⤳ a ⤳ bool)
  ≔ λ x y, !! (x == y);
notation !== infix 5;

// ------- free variables ----------------
// when `t : exp` or `t : prd`,
//  `free x t ≡ true` if `x` occurs free in `t`.
sequential symbol free [a : Set] : El (str ⤳ a ⤳ bool);

// define `free x` on `prd`.
rule free $x ($P and $Q)  ↪ (free $x $P) <> (free $x $Q)
with free $x ($P or $Q)   ↪ (free $x $P) <> (free $x $Q)
with free $x ($P => $Q)   ↪ (free $x $P) <> (free $x $Q)
with free $x ($P <=> $Q)  ↪ (free $x $P) <> (free $x $Q)
with free $x (not $P)     ↪ free $x $P
with free $x (! $vs $P)   ↪ (free $x $P) && !! ($x ⋿ $vs)
with free $x (# $vs $P)   ↪ (free $x $P) && !! ($x ⋿ $vs)
with free $x ($e1 = $e2)  ↪ (free $x $e1) <> (free $x $e2)
with free $x FAUX ↪ false
with free $x VRAI ↪ false
with free $x (Ψ $e) ↪ (free $x $e)
with free $x ($e1 ∈ $e2) ↪ (free $x $e1) <> (free $x $e2);

// define `free x` on `exp`.
rule free $x (var $y) ↪ ($x == $y)
with free $x (ι _)    ↪ false
with free $x ($e1 ‵ $e2) ↪ (free $x $e1) <> (free $x $e2)
with free $x ($e1 ∥ $e2) ↪ (free $x $e1) <> (free $x $e2);

// ------- free variables ----------------
// if `t : exp` or `t : prd`, then `subst x e t` is the result of rewriting
// all free occurrences of `x` in `t` with `e`.
sequential symbol subst [a : Set] : El (str ⤳ exp ⤳ a ⤳ a);

// define `subst x e` on `prd`.
rule subst $x $t ($P and $Q)  ↪ (subst $x $t $P) and (subst $x $t $Q)
with subst $x $t ($P or $Q)   ↪ (subst $x $t $P) or (subst $x $t $Q)
with subst $x $t ($P => $Q)   ↪ (subst $x $t $P) => (subst $x $t $Q)
with subst $x $t ($P <=> $Q)  ↪ (subst $x $t $P) <=> (subst $x $t $Q)
with subst $x $t (not $P)     ↪ not (subst $x $t $P)
with subst $x $t (! $vs $P)   ↪ ite ($x ⋿ $vs) (! $vs $P) (! $vs (subst $x $t $P))
with subst $x $t (# $vs $P)   ↪ ite ($x ⋿ $vs) (# $vs $P) (# $vs (subst $x $t $P))
with subst $x $t ($e1 = $e2)  ↪ (subst $x $t $e1) = (subst $x $t $e2)
with subst $x $t (Ψ $p)       ↪ Ψ (subst $x $t $p);

// define `subst x e` on `exp`.
rule subst $x $t (var $y) ↪ ite ($x == $y) $t (var $y)
with subst $x $t ($f ‵ $y) ↪ (subst $x $t $f) ‵ (subst $x $t $y);

// ------- operations exclusively for AND5 ---------------------------

// check if a predicate appears in an n-ary conjunction.
sequential symbol elem_conj : El (prd ⤳ prd ⤳ bool);
rule elem_conj $P ($P and $xs) ↪ true
with elem_conj $P ($Q and $xs) ↪ elem_conj $P $xs
with elem_conj $P _            ↪ false;

// replace a conjunct in an n-ary conjunction.
sequential symbol repl_conj : El (prd ⤳ prd ⤳ prd ⤳ prd);
rule repl_conj $Q $Q' ($Q and $xs) ↪ ($Q' and $xs)
with repl_conj $Q $Q' ($P and $xs) ↪ ($P  and (repl_conj $Q $Q' $xs))
with repl_conj _  _   $R           ↪ $R;
