require open
  Stdlib.Prop
  Stdlib.String
  Stdlib.Z;

// datatype for variable-lists.
inductive Var : TYPE ≔
  | id : String → Var
  | ⨾ : Var → Var → Var;
notation ⨾ infix right 5;

// datatypes for predicates, expressions, and sets:
inductive Prd : TYPE ≔
  | ∧ : Prd → Prd → Prd
  | ⇒ : Prd → Prd → Prd
  | ¬ : Prd → Prd
  | ∀ : Var → Prd → Prd
  | = : Exp → Exp → Prd
  | ∈ : Exp → Exp → Prd
with Exp : TYPE ≔
  | #var : Var → Exp
  | ↦ : Exp → Exp → Exp
  | × : Exp → Exp → Exp
  | 𝒫 : Exp → Exp
  | big : Exp
  | choice : Exp → Exp
  | comp : Var → Prd → Exp;

symbol #id ≔ λ str, #var (id str);

// coercion rules for variables and sets:
coerce_rule coerce Var Exp $x ↪ #var $x;

// infix notation for predicates:
notation ¬ prefix 10;
notation ∧ infix left 9;
notation ⇒ infix left 8;

// logical disjunction and equivalence.
symbol ∨ ≔ λ p q, ¬ p ⇒ q;
symbol ⇔ ≔ λ p q, (p ⇒ q) ∧ (q ⇒ p);
notation ∨ infix left 9;
notation ⇔ infix left 7;

// infix notation for maplets and products.
notation ↦ infix 5;
notation × infix 5;

// infix notation for membership and equality.
notation ∈ infix left 15;
notation = infix 5;


sequential symbol bSet : Exp → 𝔹;
rule bSet ($E ↦ $F) ↪ false
with bSet (choice $E) ↪ bSet $E
with bSet ($E × $F) ↪ (bSet $E) and (bSet $F)
with bSet (𝒫 $E) ↪ bSet $E
with bSet (comp $x $P) ↪ true
with bSet big ↪ true;


// define disequality.
symbol != ≔ λ E F, ¬ (E = F);
notation != infix 20;

// define ⊆ inclusion.
symbol ⊆ ≔ λ s t, s ∈ 𝒫 t;
notation ⊆ infix 10;

// define ⊂ inclusion.
symbol ⊂ ≔ λ s t, (s ⊆ t) ∧ (s != t);
notation ⊂ infix 10;

// syntactic equality:
sequential symbol var_eq : Var → Var → 𝔹;
sequential symbol exp_eq : Exp → Exp → 𝔹;
sequential symbol prd_eq : Prd → Prd → 𝔹;

rule var_eq $x $x ↪ true
with var_eq _ _ ↪ false;

// core expressions.
rule exp_eq (#var $x) (#var $y) ↪ var_eq $x $y
with exp_eq ($E ↦ $F) ($G ↦ $H)
  ↪ (exp_eq $E $G) and (exp_eq $F $H)
with exp_eq (choice $s) (choice $t) ↪ exp_eq $s $t
// set expressions.
with exp_eq ($s × $t) ($u × $v)
  ↪ (exp_eq $s $u) and (exp_eq $t $v)
with exp_eq (𝒫 $s) (𝒫 $t) ↪ exp_eq $s $t
with exp_eq (big) (big) ↪ true
with exp_eq (comp $x $P) (comp $y $Q)
  ↪ (var_eq $x $y) and (prd_eq $P $Q)
with exp_eq _ _ ↪ false;


// defined on predicates thus:
rule prd_eq ($p ∧ $q) ($r ∧ $s)
  ↪ (prd_eq $p $r) and (prd_eq $q $s)
with prd_eq ($p ⇒ $q) ($r ⇒ $s)
  ↪ (prd_eq $p $r) and (prd_eq $q $s)
with prd_eq (¬ $p) (¬ $q)
  ↪ (prd_eq $p $q)
with prd_eq (∀ $x $p) (∀ $y $q)
  ↪ (var_eq $x $y) and (prd_eq $p $q)
with prd_eq ($e = $f) ($g = $h)
  ↪ (exp_eq $e $g) and (exp_eq $f $h)
with prd_eq ($e ∈ $s) ($f ∈ $t)
  ↪ (exp_eq $e $f) and (exp_eq $s $t)
with prd_eq _ _ ↪ false;
// end.


// datatype for B-formulas: i.e., either expr or pred.
inductive Frm : TYPE ≔
  | #exp : Exp → Frm
  | #prd : Prd → Frm;

// syntactic equality on formulas.
sequential symbol == : Frm → Frm → 𝔹;
notation == infix 10;
rule (#exp $E == #exp $F) ↪ exp_eq $E $F
with (#prd $P == #prd $Q) ↪ prd_eq $P $Q
with (_ == _) ↪ false;

// coercion rules for Exp -> Frm, Prd -> Frm.
coerce_rule coerce Exp Frm $e ↪ #exp $e;
coerce_rule coerce Prd Frm $p ↪ #prd $p;

// boolean-guarded expression.
symbol ?exp : Exp → 𝔹 → Exp;
rule ?exp $E true ↪ $E;

// boolean-guarded predicate.
symbol ?prd : Prd → 𝔹 → Prd;
rule ?prd $P true ↪ $P;

// non-free. see NonFree.lp
symbol nf : Var → Frm → 𝔹;
symbol pnf : Var → Prd → 𝔹;
symbol enf : Var → Exp → 𝔹;

rule nf $x (#prd $P) ↪ pnf $x $P
with nf $x (#exp $E) ↪ enf $x $E;

// substitution. see Subst.lp
symbol sub : Var → Exp → Frm → Frm;
symbol psub : Var → Exp → Prd → Prd;
symbol esub : Var → Exp → Exp → Exp;

rule sub $x $E (#prd $P) ↪ #prd (psub $x $E $P)
with sub $x $E (#exp $F) ↪ #exp (esub $x $E $F);

// datatype for B-types.
inductive bTyp : TYPE ≔
  | super : Exp → bTyp
  | typ : Exp → bTyp
  | ∗ : bTyp → bTyp → bTyp
  | ℙ : bTyp → bTyp
  | iden : String → bTyp;

// infix notation for type-level product.
notation ∗ infix right 10;

// datatype for B-type-predicates.
inductive bTypPrd : TYPE ≔
  | check : Prd → bTypPrd
  | ty_eq : bTyp → bTyp → bTypPrd;


// `prf p` is the type of proofs of `p`
constant symbol prf : Prd → TYPE;
symbol ▷ ≔ prf; notation ▷ prefix 5;

// `j : judge p` iff `j` derives the typing-predicate `p`.
constant symbol judge : bTypPrd → TYPE;

// `j : ✓ p` iff `j` derives `check p`.
symbol ✓ (p : Prd) : TYPE ≔ judge (check p);

// `j : t ≣ t'` iff `j` derives `ty_eq t t'`.
symbol ≣ (t t' : bTyp) : TYPE ≔ judge (ty_eq t t');
notation ≣ infix 5;


symbol symm [U T] : (U ≣ T) → (T ≣ U);

symbol given : Exp → TYPE;

symbol T1 [P Q : Prd]
  : ✓ P → ✓ Q → ✓ (P ∧ Q);

symbol T2 [P Q : Prd]
  : ✓ P → ✓ Q → ✓ (P ⇒ Q);

symbol T3 [P : Prd]
  : ✓ P → ✓ (¬ P);

symbol T4 [x : Var] [s : Exp] [P : Prd]
  : (▷ (x ∈ s) → ✓ P) → ✓ (∀ x (x ∈ s ⇒ P));

symbol T5 [x y : Var] [s t : Exp] [P : Prd]
  : ✓ (∀ x (x ∈ s ⇒ ∀ y (y ∈ t ⇒ P)))
  → ✓ (∀ (x ⨾ y) ((x ↦ y) ∈ (s × t) ⇒ P));

symbol T6 [x : Var] [P Q R : Prd]
  : ✓ (∀ x (P ⇒ Q ∧ R))
  → ✓ (∀ x (P ∧ Q ⇒ R));

symbol T7 [E F : Exp]
  : (typ E ≣ typ F) → ✓ (E = F);

symbol T8 [E s : Exp]
  : (typ E ≣ super s) → ✓ (E ∈ s);

symbol T8' [s t : Exp]
  : (super s ≣ super t) → ✓ (s ⊆ t);

symbol T9 [x : Var] [s : Exp] [U : bTyp]
  : ▷ (x ∈ s) → (super s ≣ U) → (typ x ≣ U);

symbol T10 [E F : Exp] [U : bTyp]
  : (typ E ∗ typ F ≣ U) → (typ (E ↦ F) ≣ U);

symbol T11 [s : Exp] [U : bTyp]
  : (super s ≣ U) → (typ (choice s) ≣ U);

symbol T12 [s : Exp] [U : bTyp]
  : (ℙ (super s) ≣ U) → (typ s ≣ U);

symbol T13 [x : Var] [s : Exp] [U : bTyp]
  : ▷ (x ∈ s)
  → (super s ≣ ℙ U)
  → (super x ≣ U);

symbol T13' [x : Var] [s : Exp] [U : bTyp]
  : ▷ (x ∈ s)
  → (ℙ U ≣ super s)
  → (U ≣ super x)
  ≔ λ h1 h2, symm (T13 h1 (symm h2));

symbol T14 [s t : Exp] [U : bTyp]
  : (super s ∗ super t ≣ U)
  → (super (s × t) ≣ U);

symbol T15 [s : Exp] [U : bTyp]
  : (ℙ (super s) ≣ U)
  → (super (𝒫 s) ≣ U);

symbol T15' [s : Exp] [U : bTyp]
  : (U ≣ ℙ (super s))
  → (U ≣ super (𝒫 s))
  ≔ λ h, symm (T15 (symm h));

symbol T16 [x : Var] [s : Exp] [P : Prd] [U : bTyp]
  : ✓ (∀ x (x ∈ s ⇒ P))
  → (super s ≣ U)
  → (super (comp x (x ∈ s ∧ P)) ≣ U);

symbol T17 [I : String] [U : bTyp]
  : given (#id I)
  → (iden I ≣ U)
  → (super (#id I) ≣ U);

symbol T17' [I : String] [U : bTyp]
  (h1 : given (#id I))
  (h2 : U ≣ iden I)
  : (U ≣ super (#id I))
  ≔ symm (T17 h1 (symm h2));

symbol T18 [s : Exp] [U : bTyp]
  : (super s ≣ ℙ U)
  → (super (choice s) ≣ U);

symbol T19 [T U : bTyp]
  : (T ≣ U)
  → (ℙ T ≣ ℙ U);

symbol T20 [T U V W : bTyp]
  : (T ≣ U)
  → (V ≣ W)
  → (T ∗ V ≣ U ∗ W);

symbol T21 [I : String]
  : given (#id I)
  → (iden I ≣ iden I);

// example of a type-checking derivation.
symbol tc_example
  (h : given (#id "s"))
  :
  let a : Var ≔ id "a" in
  let b : Var ≔ id "b" in
  let x : Var ≔ id "x" in
  let y : Var ≔ id "y" in
  let s : Exp ≔ #id "s" in
  ✓ (∀ (a ⨾ b) (
    ((a ↦ b) ∈ ((𝒫 s) × (𝒫 s)))
    ⇒ (comp x (x ∈ s ∧ (x ∈ a ∧ x ∈ b)) ⊆ s))
  )
  ≔
  begin
    assume h;
    apply T5;
    apply T4; assume a;
    apply T4; assume b;
    apply T8';
    apply T17' h;
    apply T16
    {
      apply T4; assume x;
      apply T1
      {
        apply T8; apply T13' a;
        apply T15'; apply T19;
        apply T17' h; apply T9 x;
        apply T17 h; apply T21 h;
      } {
        apply T8; apply T13' b;
        apply T15'; apply T19;
        apply T17' h; apply T9 x;
        apply T17 h; apply T21 h;
      }
    }{
      apply T17 h;
      apply T21 h;
    }
  end;

type tc_example;
