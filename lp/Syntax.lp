require open Logic.U.Set Logic.U.Prop;
require open Logic.U.Arrow Logic.U.DepArrow Logic.U.Quant;
require open pp2lp.Prelude;

// ------ predicates, expressions, formulas ------
symbol idt : Set ≔ string;
symbol vrb : Set ≔ list idt;
symbol prd : Set;
symbol exp : Set;
symbol frm : Set;

// ------ primitive logical symbols --------------
injective symbol and  : El (prd ⤳ prd ⤳ prd);
injective symbol or   : El (prd ⤳ prd ⤳ prd);
injective symbol =>   : El (prd ⤳ prd ⤳ prd);
injective symbol <=>  : El (prd ⤳ prd ⤳ prd);
injective symbol not  : El (prd ⤳ prd);
injective symbol =    : El (exp ⤳ exp ⤳ prd);
injective symbol atom : El (frm ⤳ prd);
injective symbol ! : El (vrb ⤳ prd ⤳ prd);
injective symbol # : El (vrb ⤳ prd ⤳ prd);
injective symbol var : El (idt ⤳ exp);

notation =   infix left 2;
notation and infix left 2;
notation or  infix left 2;
notation =>  infix left 2;
notation <=> infix left 1;
notation not prefix 3;

// mystery quantifiers
injective symbol ♢ : El (vrb ⤳ prd ⤳ prd);  // aka. forall
injective symbol ♡ : El (vrb ⤳ prd ⤳ prd); // aka. forall2

symbol VRAI : El prd;
symbol FAUX : El prd;

// not equal
injective symbol != (a b : El exp) ≔ not (a = b);
notation !=  infix left 2;

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

rule ((==) [string] $x $x) ↪ true
with ((==) [string] _  _)  ↪ false;

rule FAUX == FAUX ↪ true
with VRAI == VRAI ↪ true
with (not $p) == (not $q)           ↪ ($p == $q)
with ($p1 and $p2) == ($q1 and $q2) ↪ ($p1 == $q1) && ($p2 == $q2)
with ($p1 or $p2) == ($q1 or $q2)   ↪ ($p1 == $q1) && ($p2 == $q2)
with ($p1 => $p2) == ($q1 => $q2)   ↪ ($p1 == $q1) && ($p2 == $q2)
with ($p1 <=> $p2) == ($q1 <=> $q2) ↪ ($p1 == $q1) && ($p2 == $q2)
with ($e1 = $e2) == ($f1 = $f2)     ↪ ($e1 == $f1) && ($e2 == $f2);
//with ($e1 !== $e2) == ($f1 !== $f2)   ↪ ($e1 == $f1) && ($e2 == $f2);
//with (! $P) == (! $Q) ↪ (`∀ x, ($P x == $Q x))
//with (# $P) == (# $Q) ↪ (`∀ x, ($P x == $Q x))
//with (♢ $P) == (♢ $Q) ↪ (`∀ x, ($P x == $Q x))
//with (♡ $P) == (♡ $Q) ↪ (`∀ x, ($P x == $Q x`));

// ------- free vars, substitution ----------------
symbol free [a : Set] : El (idt ⤳ a ⤳ bool);

rule free $x (var $y) ↪ ($x == $y);

rule free $x ($P and $Q)  ↪ (free $x $P) <> (free $x $Q)
with free $x ($P or $Q)   ↪ (free $x $P) <> (free $x $Q)
with free $x ($P => $Q)   ↪ (free $x $P) <> (free $x $Q)
with free $x ($P <=> $Q)  ↪ (free $x $P) <> (free $x $Q)
with free $x (not $P)     ↪ free $x $P
with free $x (! $vs $P)   ↪ (free $x $P) && !! ($x ∈ $vs)
with free $x (# $vs $P)   ↪ (free $x $P) && !! ($x ∈ $vs)
with free $x ($e1 = $e2)  ↪ (free $x $e1) <> (free $x $e2)
with free $x (atom $f)    ↪ (free $x $f)
with free $x FAUX ↪ false
with free $x VRAI ↪ false;

symbol subst [a : Set] : El (idt ⤳ exp ⤳ a ⤳ a);
//rule subst $x $t (VAR $y)     ↪ ite ($x == $y) $t (VAR $y)
//with subst $x $t (AND $P $Q)  ↪ AND (subst $x $t $P) (subst $x $t $Q)
//with subst $x $t (OR $P $Q)   ↪ OR (subst $x $t $P) (subst $x $t $Q)
//with subst $x $t (IMPL $P $Q) ↪ IMPL (subst $x $t $P) (subst $x $t $Q)
//with subst $x $t (IFF $P $Q)  ↪ IFF (subst $x $t $P) (subst $x $t $Q)
//with subst $x $t (NOT $P)     ↪ NOT (subst $x $t $P)
//with subst $x $t (ALL $vs $P) ↪ ite ($x ∈ $vs) (ALL $vs $P) (ALL $vs (subst $x $t $P))
//with subst $x $t (EXI $vs $P) ↪ ite ($x ∈ $vs) (EXI $vs $P) (EXI $vs (subst $x $t $P))
//with subst $x $t (EQ $e1 $e2) ↪ EQ (subst $x $t $e1) (subst $x $t $e2)
//with subst $x $t (ATOM $f)    ↪ ATOM (subst $x $t $f);

// evaluation
symbol ev [a : Set] [b : Set] : El (a ⤳ b);

// ordered pairs, set equality ??
symbol opair : El (exp ⤳ exp ⤳ exp);
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

 constant symbol Tactic : TYPE;

  constant symbol #admit : Tactic;
  builtin "admit" ≔ #admit;

  symbol & : Tactic → Tactic → Tactic;
  builtin "and" ≔ &;
  notation & infix right 10;

  constant symbol #apply [p] : El p → Tactic;
  builtin "apply" ≔ #apply;

  constant symbol #assume : String → Tactic;
  builtin "assume" ≔ #assume;

  constant symbol #change [p] : Prf p → Tactic;
  builtin "change" ≔ #change;

  constant symbol #fail : Tactic;
  builtin "fail" ≔ #fail;

  constant symbol #generalize : Π [a], El a → Tactic;
  builtin "generalize" ≔ #generalize;

  constant symbol #have : String → Prop → Tactic;
  builtin "have" ≔ #have;

  constant symbol #induction : Tactic;
  builtin "induction" ≔ #induction;

  constant symbol #orelse : Tactic → Tactic → Tactic;
  builtin "orelse" ≔ #orelse;

  constant symbol #refine : String → Tactic;
  builtin "refine" ≔ #refine;

  constant symbol #reflexivity : Tactic;
  builtin "reflexivity" ≔ #reflexivity;

  constant symbol #remove : Π [a], Prf a → Tactic;
  builtin "remove" ≔ #remove;

  constant symbol #repeat : Tactic → Tactic;
  builtin "repeat" ≔ #repeat;

  constant symbol #rewrite_gen : String → String → Π [p], Prf p → Tactic;
  builtin "rewrite" ≔ #rewrite_gen;

  symbol #rewrite : Π [p], Prf p → Tactic ≔ @#rewrite_gen "" "";

  constant symbol #set : String → Π [a], Prf a → Tactic;
  builtin "set" ≔ #set;

  constant symbol #simplify : /* Π [a], τ a → */ Tactic;
  builtin "simplify" ≔ #simplify;

  constant symbol #simplify_beta : Tactic;
  builtin "simplify rule off" ≔ #simplify_beta;

  constant symbol #solve : Tactic;
  builtin "solve" ≔ #solve;

  constant symbol #symmetry : Tactic;
  builtin "symmetry" ≔ #symmetry;

  constant symbol #try : Tactic → Tactic;
  builtin "try" ≔ #try;

  constant symbol #why3 : /*τ (option string) →*/ Tactic;
  builtin "why3" ≔ #why3;
