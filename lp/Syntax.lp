require open Logic.U.Set Logic.U.Prop;
require open Logic.U.Arrow Logic.U.DepArrow Logic.U.Quant;
require open pp2lp.Prelude;



// ------ predicates, expressions, formulas ------
symbol idt ≔ string;
symbol vrb ≔ list idt;

symbol Frm : TYPE;

inductive Exp : TYPE ≔
  | VAR : El idt → Exp
  | ZERO : Exp
  | ONE : Exp
  | MINUS : Exp → Exp → Exp
  | ADD : Exp → Exp → Exp
  | SUB : Exp → Exp → Exp
with Prd : TYPE ≔
  | AND : Prd → Prd → Prd
  | OR  : Prd → Prd → Prd
  | IMPL : Prd → Prd → Prd
  | IFF  : Prd → Prd → Prd
  | NOT : Prd → Prd
  | ALL : El vrb → Prd → Prd
  | EXI : El vrb → Prd → Prd
  | EQ  : Exp → Exp → Prd
  | ATOM : Frm → Prd;

symbol prd : Set;
symbol exp : Set;
symbol frm : Set;

rule El prd ↪ Prd;
rule El exp ↪ Exp;
rule El frm ↪ Frm;



// ------ primitive logical symbols --------------
injective symbol and  ≔ AND;
injective symbol or   ≔ OR;
injective symbol =>   ≔ IMPL;
injective symbol <=>  ≔ IFF;
injective symbol not  ≔ NOT;
injective symbol =    ≔ EQ;
injective symbol atom ≔ ATOM;
injective symbol ! ≔ ALL;
injective symbol # ≔ EXI;

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
symbol Seq ≔ El seq;
injective symbol ⟝ : El ((list prd) ⤳ prd ⤳ seq);
notation ⟝ infix 0;

// sequent derivations
injective symbol ▷ : El seq → TYPE;
injective symbol ⊩ : El (list prd) → El prd → Set;
notation ⊩ infix 0;
rule El ($H ⊩ $P) ↪ ▷ ($H ⟝ $P);

// type-level side-conditions
symbol If : El bool → Set → TYPE;
rule If ⊤ $X ↪ El $X;

symbol Thm : Prd → TYPE ≔
  λ p, (▷ (nil ⟝ p));


// ---- Results ------------------------------
injective symbol Res : Seq → TYPE;
symbol obtain [Σ : Seq] : Res Σ → El prd;

coerce_rule coerce (Res $Σ) Prd $ρ ↪ obtain $ρ;

// ----- Operations on terms -----------------------

// syntactic equality on expressions and predicates.
sequential symbol == [a : Set] : El (a ⤳ a ⤳ bool);
sequential symbol !== [a : Set] : El (a ⤳ a ⤳ bool);

notation == infix 5;
notation !== infix 5;

rule ($X !== $Y) ↪ ite ($X == $Y) ⊥ ⊤;

rule ((==) [string] $x $x) ↪ ⊤
with ((==) [string] _  _)  ↪ ⊥;

rule FAUX == FAUX ↪ ⊤
with VRAI == VRAI ↪ ⊤
with (not $p) == (not $q)           ↪ ($p == $q)
with ($p1 and $p2) == ($q1 and $q2) ↪ ($p1 == $q1) ∧ ($p2 == $q2)
with ($p1 or $p2) == ($q1 or $q2)   ↪ ($p1 == $q1) ∧ ($p2 == $q2)
with ($p1 => $p2) == ($q1 => $q2)   ↪ ($p1 == $q1) ∧ ($p2 == $q2)
with ($p1 <=> $p2) == ($q1 <=> $q2) ↪ ($p1 == $q1) ∧ ($p2 == $q2)
with ($e1 = $e2) == ($f1 = $f2)     ↪ ($e1 == $f1) ∧ ($e2 == $f2)
with ($e1 != $e2) == ($f1 != $f2)   ↪ ($e1 == $f1) ∧ ($e2 == $f2);
//with (! $P) == (! $Q) ↪ (`∀ x, ($P x == $Q x))
//with (# $P) == (# $Q) ↪ (`∀ x, ($P x == $Q x))
//with (♢ $P) == (♢ $Q) ↪ (`∀ x, ($P x == $Q x))
//with (♡ $P) == (♡ $Q) ↪ (`∀ x, ($P x == $Q x`));


// ------- free vars, substitution ----------------
symbol free [a : Set] : El (idt ⤳ a ⤳ bool);
rule free $x (AND $P $Q)  ↪ (free $x $P) ∨ (free $x $Q)
with free $x (OR $P $Q)   ↪ (free $x $P) ∨ (free $x $Q)
with free $x (IMPL $P $Q) ↪ (free $x $P) ∨ (free $x $Q)
with free $x (IFF $P $Q)  ↪ (free $x $P) ∨ (free $x $Q)
with free $x (NOT $P)     ↪ free $x $P
with free $x (ALL $vs $P) ↪ (free $x $P) ∧ ¬($x ∈ $vs)
with free $x (EXI $vs $P) ↪ (free $x $P) ∧ ¬($x ∈ $vs)
with free $x (EQ $e1 $e2) ↪ (free $x $e1) ∨ (free $x $e2)
with free $x (ATOM $f)    ↪ free $x $f;

symbol subst [a : Set] : El (idt ⤳ exp ⤳ a ⤳ a);
rule subst $x $t (VAR $y)     ↪ ite ($x == $y) $t (VAR $y)
with subst $x $t (AND $P $Q)  ↪ AND (subst $x $t $P) (subst $x $t $Q)
with subst $x $t (OR $P $Q)   ↪ OR (subst $x $t $P) (subst $x $t $Q)
with subst $x $t (IMPL $P $Q) ↪ IMPL (subst $x $t $P) (subst $x $t $Q)
with subst $x $t (IFF $P $Q)  ↪ IFF (subst $x $t $P) (subst $x $t $Q)
with subst $x $t (NOT $P)     ↪ NOT (subst $x $t $P)
with subst $x $t (ALL $vs $P) ↪ ite ($x ∈ $vs) (ALL $vs $P) (ALL $vs (subst $x $t $P))
with subst $x $t (EXI $vs $P) ↪ ite ($x ∈ $vs) (EXI $vs $P) (EXI $vs (subst $x $t $P))
with subst $x $t (EQ $e1 $e2) ↪ EQ (subst $x $t $e1) (subst $x $t $e2)
with subst $x $t (ATOM $f)    ↪ ATOM (subst $x $t $f);

// evaluation
symbol ev [a : Set] [b : Set] : El (a ⤳ b);

// ordered pairs, set equality ??
symbol opair : El (exp ⤳ exp ⤳ exp);
symbol eql_set : El (exp ⤳ exp ⤳ prd);

// operations for finding/replacing a term within an n-ary conjunction.
sequential symbol elem_conj : El (prd ⤳ prd ⤳ bool);
rule elem_conj $P ($P and $xs) ↪ ⊤
with elem_conj $P ($Q and $xs) ↪ elem_conj $P $xs
with elem_conj $P _          ↪ ⊥;

sequential symbol repl_conj : El (prd ⤳ prd ⤳ prd ⤳ prd);
rule repl_conj $Q $Q' ($Q and $xs) ↪ ($Q' and $xs)
with repl_conj $Q $Q' ($P and $xs) ↪ ($P  and (repl_conj $Q $Q' $xs))
with repl_conj _  _   $R           ↪ $R;
