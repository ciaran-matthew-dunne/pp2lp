require open Logic.U.Set Logic.U.Prop Logic.U.Arrow Logic.U.Quant;
require open pp2lp.Prelude;

// ------ predicates, expressions, formulas ------

symbol idt ≔ string;
symbol vrb ≔ list idt;

symbol EXP : TYPE;
symbol FRM : TYPE;

inductive PRD : TYPE ≔
  | AND : PRD → PRD → PRD
  | OR  : PRD → PRD → PRD
  | IMPL : PRD → PRD → PRD
  | IFF  : PRD → PRD → PRD
  | NOT : PRD → PRD
  | ALL : El vrb → PRD → PRD
  | EXI : El vrb → PRD → PRD
  | EQ  : EXP → EXP → PRD
  | ATOM : FRM → PRD;

symbol prd : Set;
symbol exp : Set;
symbol frm : Set;

rule El prd ↪ PRD;
rule El exp ↪ EXP;

// inject identifiers into expressions.
injective symbol var : El (idt ⤳ exp);


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




// ------ Sequents ---------------------------

// sequents
symbol seq : Set;
injective symbol ⟝ : El ((list prd) ⤳ prd ⤳ seq);
notation ⟝ infix 0;

// sequents-as-types
symbol ▷ : El seq → Set;

// results
symbol ⟿ : El seq → El prd → Set;
notation ⟿ infix 0;

// exceptions
symbol ∅ : Set;

// conditional
symbol ⇛ : Prop → Set → Set;
notation ⇛ infix right 0;
rule ⊤ ⇛ $x ↪ $x
with ⊥ ⇛ _  ↪ ∅;

// substitution
symbol subst_prd : El (idt ⤳ exp ⤳ prd ⤳ prd);
symbol subst_exp : El (idt ⤳ exp ⤳ exp ⤳ exp);
symbol subst_frm : El (idt ⤳ exp ⤳ frm ⤳ frm);

rule (subst_prd $x $e ($p1 and $p2)) ↪ (subst_prd $x $e $p1) and (subst_prd $x $e $p2)
with (subst_prd $x $e ($p1 or $p2)) ↪ (subst_prd $x $e $p1) or (subst_prd $x $e $p2)
with (subst_prd $x $e ($p1 => $p2)) ↪ (subst_prd $x $e $p1) => (subst_prd $x $e $p2)
with (subst_prd $x $e ($p1 <=> $p2)) ↪ (subst_prd $x $e $p1) <=> (subst_prd $x $e $p2)
with (subst_prd $x $e (not $p)) ↪ not (subst_prd $x $e $p)
with (subst_prd $x $e ($e1 = $e2)) ↪ (subst_exp $x $e $e1) = (subst_exp $x $e $e1);
//with (subst_prd $x $e (! $xs $p)) ↪ ...
//with (subst_prd $x $e (! $xs $p)) ↪ ...

// ----- Misc symbols -----------------------

// not equal
injective symbol != (a b : El exp) ≔ not (a = b);
notation !=  infix left 2;

// booleans
symbol VRAI : El prd;
symbol FAUX : El prd;

// mystery quantifiers
injective symbol forall : El (vrb ⤳ prd ⤳ prd);  // aka. ♢
injective symbol forall2 : El (vrb ⤳ prd ⤳ prd); // aka. ♡

// some macros for quantifiers
symbol ∀1 (s : String) : El (prd ⤳ prd) ≔ ! (s ∷ nil);
symbol ∃1 (s : String) : El (prd ⤳ prd) ≔ # (s ∷ nil);
symbol ♢1 (s : String) : El (prd ⤳ prd) ≔ forall (s ∷ nil);
symbol ♡1 (s : String) : El (prd ⤳ prd) ≔ forall2 (s ∷ nil);

symbol ∀2 (s1 s2 : String) : El (prd ⤳ prd) ≔ ! (s1 ∷ s2 ∷ nil);
symbol ∃2 (s1 s2 : String) : El (prd ⤳ prd) ≔ # (s1 ∷ s2 ∷ nil);
symbol ♢2 (s1 s2 : String) : El (prd ⤳ prd) ≔ forall (s1 ∷ s2 ∷ nil);
symbol ♡2 (s1 s2 : String) : El (prd ⤳ prd) ≔ forall2 (s1 ∷ s2 ∷ nil);

// arithmetic
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



// ----- Operations on terms -----------------------

// syntactic equality on predicates
rule FAUX ≣ FAUX ↪ ⊤
with VRAI ≣ VRAI ↪ ⊤
with (not $p) ≣ (not $q)           ↪ ($p ≣ $q)
with ($p1 and $p2) ≣ ($q1 and $q2) ↪ ($p1 ≣ $q1) ∧ ($p2 ≣ $q2)
with ($p1 or $p2) ≣ ($q1 or $q2)   ↪ ($p1 ≣ $q1) ∧ ($p2 ≣ $q2)
with ($p1 => $p2) ≣ ($q1 => $q2)   ↪ ($p1 ≣ $q1) ∧ ($p2 ≣ $q2)
with ($p1 <=> $p2) ≣ ($q1 <=> $q2) ↪ ($p1 ≣ $q1) ∧ ($p2 ≣ $q2)
with ($e1 = $e2) ≣ ($f1 = $f2)     ↪ ($e1 ≣ $f1) ∧ ($e2 ≣ $f2)
with ($e1 != $e2) ≣ ($f1 != $f2)   ↪ ($e1 ≣ $f1) ∧ ($e2 ≣ $f2);
//with (! $P) ≣ (! $Q) ↪ (`∀ x, ($P x ≣ $Q x))
//with (# $P) ≣ (# $Q) ↪ (`∀ x, ($P x ≣ $Q x))
//with (♢ $P) ≣ (♢ $Q) ↪ (`∀ x, ($P x ≣ $Q x))
//with (♡ $P) ≣ (♡ $Q) ↪ (`∀ x, ($P x ≣ $Q x`));

// evaluation
symbol ev [a : Set] [b : Set] : El (a ⤳ b);

// ordered pairs, set equality ??
symbol opair : El (exp ⤳ exp ⤳ exp);
symbol eql_set : El (exp ⤳ exp ⤳ prd);

sequential symbol unfold_conj : El (prd ⤳ list prd);
rule unfold_conj ($x and $xs) ↪ cons $x (unfold_conj $xs)
with unfold_conj $p           ↪ nil;

sequential symbol fold_conj : El (list prd ⤳ prd);
rule fold_conj ($x ∷ nil) ↪ $x
with fold_conj ($x ∷ $xs) ↪ $x and (fold_conj $xs)
with fold_conj nil        ↪ FAUX;
