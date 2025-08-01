require open Logic.U.Set Logic.U.Prop;
require open Logic.U.Arrow Logic.U.DepArrow Logic.U.Quant;
require open pp2lp.Prelude;

// ------ predicates, expressions, formulas ------
symbol 𝕊 : TYPE;
builtin "String" ≔ 𝕊;

symbol str : Set;
rule El str ↪ 𝕊;

symbol vrb : Set ≔ list str;
symbol prd : Set;
symbol exp : Set;
symbol idv : Set; // individuals, sets, etc.
//symbol frm : Set;

// cast an expression to a predicate.
injective symbol Ψ : El exp → El prd;
coerce_rule coerce (El exp) (El prd) $p ↪ Ψ $p;

injective symbol ι : El idv → El exp;
coerce_rule coerce (El idv) (El exp) $x ↪ ι $x;
coerce_rule coerce (El idv) (El prd) $x ↪ Ψ (ι $x);

// TODO.
injective symbol ‵ : El (exp ⤳ exp ⤳ exp);
notation ‵ infix left 10;

injective symbol ∈ : El (exp ⤳ exp ⤳ prd);
notation ∈ infix left 2;


// ------ primitive logical symbols --------------
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

injective symbol var : El (str ⤳ exp);
coerce_rule coerce 𝕊 (El exp) $str ↪ var $str;

// quantifiers
injective symbol ! : El vrb → El prd → El prd;
injective symbol # : El (vrb ⤳ prd ⤳ prd);
injective symbol ♢ : El (vrb ⤳ prd ⤳ prd);  // aka. forall
injective symbol ♡ : El (vrb ⤳ prd ⤳ prd); // aka. forall2

symbol ⋅ : El (str ⤳ list str) ≔ λ x, cons x nil;
notation ⋅ postfix 10;

assert ⊢ ("x" ⋅) : El (list str);

symbol ⨾ : El (str ⤳ str ⤳ list str) ≔
  λ x y, cons x (cons y nil);
notation ⨾ infix right 5;


symbol VRAI : El prd;
symbol FAUX : El prd;

// not equal
injective symbol != (a b : El exp) ≔ not (a = b);
notation !=  infix left 2;

// ordered pairs
symbol ∥ : El (exp ⤳ exp ⤳ exp);
notation ∥ infix left 5;

// ----- Arithmetic -----------------------
// similarly for arithmetic relation symbols, why are these not in the grammar for prd?
symbol > : El (exp ⤳ exp ⤳ prd);
symbol ≤ : El (exp ⤳ exp ⤳ prd);
symbol < : El (exp ⤳ exp ⤳ prd);
symbol ≪ : El (exp ⤳ exp ⤳ prd);
symbol 𝟎 : El (exp);
symbol 𝟏 : El (exp);
symbol ⨪ : El (exp ⤳ exp);
symbol + : El (exp ⤳ exp ⤳ exp);
symbol - : El (exp ⤳ exp ⤳ exp);

notation > infix 5;
notation ≤ infix 5;
notation < infix 5;
notation ≪ infix 5;
notation + infix 5;
notation - infix 5;

symbol solveur [a : Set] : El (a ⤳ a);
rule solveur (Ψ $e) ↪ Ψ (solveur $e);
rule solveur (ι $p) ↪ (ι $p);

// ------ Sequents ---------------------------
symbol seq : Set;
injective symbol ⟝ : El (list prd ⤳ prd ⤳ seq);
notation ⟝ infix 0;

// sequent derivations
injective symbol ✓ : El bool → El seq → TYPE;
injective symbol ▷ : El seq → TYPE;
rule (▷ $Σ) ↪ ✓ true $Σ;

injective symbol Thm : El prd → TYPE;
rule Thm $p ↪ ▷ (nil ⟝ $p);


// ---- Results ------------------------------
injective symbol Res : El seq → TYPE;
symbol obtain [Σ : El seq] : Res Σ → El prd;
symbol result [Σ : El seq] : El prd → Res Σ;

rule obtain (result $P) ↪ $P;
coerce_rule coerce (Res $Σ) (El prd) $ρ ↪ obtain $ρ;

// ----- Operations on terms -----------------------
// syntactic equality on expressions and predicates.
sequential symbol == [a : Set] : El (a ⤳ a ⤳ bool);
notation == infix 5;

symbol !== [a : Set] : El (a ⤳ a ⤳ bool)
  ≔ λ x y, !! (x == y);
notation !== infix 5;

rule ((==) [str] $x $x) ↪ true
with ((==) [str] _  _)  ↪ false;

// syntactic equality on predicates
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

// syntactic equality on expressions
rule (var $x == var $y) ↪ ($x == $y)
with ($e1 ‵ $e2) == ($f1 ‵ $f2) ↪ ($e1 == $f1) && ($e2 == $f2)
with (ι $p) == (ι $p) ↪ true;

// otherwise, return false
rule _ == _ ↪ false;

// ------- free vars, substitution ----------------
sequential symbol free [a : Set] : El (str ⤳ a ⤳ bool);

 //defining `free` on predicates
rule free $x ($P and $Q)  ↪ (free $x $P) <> (free $x $Q)
with free $x ($P or $Q)   ↪ (free $x $P) <> (free $x $Q)
with free $x ($P => $Q)   ↪ (free $x $P) <> (free $x $Q)
with free $x ($P <=> $Q)  ↪ (free $x $P) <> (free $x $Q)
with free $x (not $P)     ↪ free $x $P
with free $x (! $vs $P)   ↪ (free $x $P) && !! ($x ⋿ $vs)
with free $x (# $vs $P)   ↪ (free $x $P) && !! ($x ⋿ $vs)
with free $x ($e1 = $e2)  ↪ (free $x $e1) <> (free $x $e2)
with free $x FAUX ↪ false
with free $x VRAI ↪ false;

rule free $x (Ψ $e) ↪ (free $x $e)
with free $x ($e1 ∈ $e2) ↪ (free $x $e1) <> (free $x $e2);

// defining `free` on expressions
rule free $x (var $y) ↪ ($x == $y)
with free $x (ι _) ↪ false
with free $x ($e1 ‵ $e2) ↪ (free $x $e1) <> (free $x $e2)
with free $x ($e1 ∥ $e2) ↪ (free $x $e1) <> (free $x $e2);
//with free $x _ ↪ false;
//with free $x ($f ‶ $y) ↪ (free $x $f) <> (free $x $y);

rule free $x (cons [exp] $y $ys)
  ↪ ite (var $x == $y) true (free $x $ys)
with free $x (nil)     ↪ false;

symbol subst [a : Set] : El (str ⤳ exp ⤳ a ⤳ a);

rule subst $x $t ($P and $Q)  ↪ (subst $x $t $P) and (subst $x $t $Q)
with subst $x $t ($P or $Q)   ↪ (subst $x $t $P) or (subst $x $t $Q)
with subst $x $t ($P => $Q)   ↪ (subst $x $t $P) => (subst $x $t $Q)
with subst $x $t ($P <=> $Q)  ↪ (subst $x $t $P) <=> (subst $x $t $Q)
with subst $x $t (not $P)     ↪ not (subst $x $t $P)
with subst $x $t (! $vs $P)   ↪ ite ($x ⋿ $vs) (! $vs $P) (! $vs (subst $x $t $P))
with subst $x $t (# $vs $P)   ↪ ite ($x ⋿ $vs) (# $vs $P) (# $vs (subst $x $t $P))
with subst $x $t ($e1 = $e2)  ↪ (subst $x $t $e1) = (subst $x $t $e2);

rule subst $x $t (var $y) ↪ ite ($x == $y) $t (var $y)
with subst $x $t (Ψ $p)   ↪ Ψ (subst $x $t $p)
with subst $x $t ($f ‵ $y) ↪ (subst $x $t $f) ‵ (subst $x $t $y);

symbol multisubst [a : Set] : El (vrb ⤳ list exp ⤳ a ⤳ a);
rule multisubst nil _ $t ↪ $t
with multisubst _ nil $t ↪ $t
with multisubst (cons $x $xs) (cons $e $es) $t ↪
  multisubst $xs $es (subst $x $e $t);

// evaluation
symbol ev [a : Set] [b : Set] : El (a ⤳ b);

// ordered pairs, set equality ??
symbol eql_set : El (exp ⤳ exp ⤳ prd);

// operations for finding/replacing a term within an n-ary conjunction.
sequential symbol elem_conj : El (prd ⤳ prd ⤳ bool);
rule elem_conj $P ($P and $xs) ↪ true
with elem_conj $P ($Q and $xs) ↪ elem_conj $P $xs
with elem_conj $P _            ↪ false;

sequential symbol repl_conj : El (prd ⤳ prd ⤳ prd ⤳ prd);
rule repl_conj $Q $Q' ($Q and $xs) ↪ ($Q' and $xs)
with repl_conj $Q $Q' ($P and $xs) ↪ ($P  and (repl_conj $Q $Q' $xs))
with repl_conj _  _   $R           ↪ $R;
