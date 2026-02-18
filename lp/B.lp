require open
  Stdlib.Prop
  Stdlib.String
  Stdlib.Z;

inductive bVar : TYPE ≔
  | IDEN : String → bVar
  | CONS : bVar → bVar → bVar;
inductive bPrd : TYPE ≔
  | AND : bPrd → bPrd → bPrd
  | IMP : bPrd → bPrd → bPrd
  | NOT : bPrd → bPrd
  | ALL : bVar → bPrd → bPrd
  | PSUB : bVar → bExp → bPrd → bPrd
  | EQ : bExp → bExp → bPrd
  | MEM : bExp → bSet → bPrd
with bExp : TYPE ≔
  | VAR : bVar → bExp
  | ESUB : bVar → bExp → bExp → bExp
  | PAIR : bExp → bExp → bExp
  | CHOICE : bSet → bExp
  | SET : bSet → bExp
with bSet : TYPE ≔
  | PROD : bSet → bSet → bSet
  | POW : bSet → bSet
  | BIG : bSet
  | COMP : bVar → bPrd → bSet;

inductive bTyp : TYPE ≔
  | SUPER : bSet → bTyp
  | TY_EXP : bExp → bTyp
  | TY_PROD : bTyp → bTyp → bTyp
  | TY_POW : bTyp → bTyp
  | TY_IDEN : String → bTyp;


inductive bTypPrd : TYPE ≔
  | CHECK : bPrd → bTypPrd
  | TY_EQ : bTyp → bTyp → bTypPrd;

constant symbol judge : bTypPrd → TYPE;
symbol ✓ (p : bPrd) : TYPE ≔ judge (CHECK p);
symbol ≣ (t t' : bTyp) : TYPE ≔ judge (TY_EQ t t');

symbol T1 [p q] : ✓ p → ✓ q → ✓ (AND p q);
symbol T2 [p q] : ✓ p → ✓ q → ✓ (IMP p q);
symbol T3 [p] : ✓ p → ✓ (NOT p);





symbol bprd : bPrd → Prop;
rule bprd (AND $p $q)      ↪ bprd $p ∧ bprd $q
with bprd (IMP $p $q)      ↪ bprd $p ⇒ bprd $q
with bprd (NOT $p)         ↪ ¬ (bprd $p);

symbol bset : bSet → Set;
symbol bexp [a] : bExp → τ a;

symbol bexp_ty (ty : String → Set) : bExp → Set;

symbol bexp_tm [a]
  (ty : String → Set) (tm : Π s : String, τ (ty s))
  : bExp → τ a;

rule bexp_aux $ty $tm (VAR (IDEN $s)) ↪ $μ $s;

// Abstract propositions for non-propositional constructors.
constant symbol eq_  : bExp → bExp → Prop;
constant symbol mem_ : bExp → bSet → Prop;
constant symbol all_ : bVar → Prop → Prop;
constant symbol psub_ : bVar → bExp → Prop → Prop;


symbol Prf : bPrd → TYPE;
rule Prf $p ↪ π (bprd     $p);

inductive Hyp : TYPE ≔
  | Prd : bPrd → Hyp
  | HCONS : Hyp → Hyp → Hyp;

inductive Seq : TYPE ≔
  SEQ : Hyp → bPrd → Seq;

symbol BR_1 [p] : (Prf p → Prf p) ≔
  begin
    assume p h;
    refine h;
  end;

//symbol BR_2 [p]
symbol BR3 [p] (h1 : Prf p) : Prf p
  ≔ BR_1 h1;

symbol BR4 [p q] :
  Prf p → (Prf p → Prf q) → Prf q ≔
  begin
    assume p q h1 h2;
    refine h2 h1;
    print;
  end;

symbol RULE_1 [p q] :
  Prf p → Prf q → Prf (AND p q);
//// ----- logic. ----------
//symbol all : (bExp → Prop) → Prop;
//notation all quantifier;
//symbol eq : bExp → bExp → Prop;

//// ----- bSet theory -----
//constant symbol mem : bExp → bSet → Prop;
//symbol ∈ ≔ mem; notation ∈ infix 10;

//constant symbol Collect : (bExp → Prop) → bSet → bSet;

//constant symbol Pow : bSet → bSet;
//symbol 𝒫 ≔ Pow;

//constant symbol choice : bSet → bExp;
//constant symbol BIG : bSet;

//// coerce a bSet to an bExpression.
//constant symbol !bSet : bSet → bExp;


//// ----- pairing and cartesian product -----
//constant symbol pair : bExp → bExp → bExp;
//constant symbol prod : bSet → bSet → bSet;
//symbol ⨾ ≔ pair; notation ⨾ infix right 5;
//symbol × ≔ prod; notation × infix right 5;

//// ----- axioms ------------------------------
//symbol bSet1 [E F s t] :
//  π ((E ⨾ F) ∈ (s × t) ⇔ (E ∈ s ∧ F ∈ t));

//symbol bSet2 [s t] :
//  π (!bSet s ∈ 𝒫 t ⇔ `all x, (x ∈ s ⇒ x ∈ t));

//symbol bSet3 [E s P] :
//  π (E ∈ Collect P s ⇔ (E ∈ s ∧ P E));

//symbol bSet4 [E s P] :
//  π (E ∈ Collect P s ⇔ (E ∈ s ∧ P E));



////type bSet;
////type (⤳);
