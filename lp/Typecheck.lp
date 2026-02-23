require open pp2lp.B;

// statically check if a term denotes a set.
sequential symbol bSet : Exp → 𝔹;
rule bSet ($E ↦ $F) ↪ false
with bSet (choice $E) ↪ bSet $E
with bSet ($E × $F) ↪ (bSet $E) and (bSet $F)
with bSet (𝒫 $E) ↪ bSet $E
with bSet (comp $x $P) ↪ true
with bSet big ↪ true;

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

//// example of a type-checking derivation.
//symbol tc_example
//  (h : given (#id "s"))
//  :
//  let a : Var ≔ id "a" in
//  let b : Var ≔ id "b" in
//  let x : Var ≔ id "x" in
//  let y : Var ≔ id "y" in
//  let s : Exp ≔ #id "s" in
//  ✓ (∀ (a ⨾ b) (
//    ((a ↦ b) ∈ ((𝒫 s) × (𝒫 s)))
//    ⇒ (comp x (x ∈ s ∧ (x ∈ a ∧ x ∈ b)) ⊆ s))
//  )
//  ≔
//  begin
//    assume h;
//    apply T5;
//    apply T4; assume a;
//    apply T4; assume b;
//    apply T8';
//    apply T17' h;
//    apply T16
//    {
//      apply T4; assume x;
//      apply T1
//      {
//        apply T8; apply T13' a;
//        apply T15'; apply T19;
//        apply T17' h; apply T9 x;
//        apply T17 h; apply T21 h;
//      } {
//        apply T8; apply T13' b;
//        apply T15'; apply T19;
//        apply T17' h; apply T9 x;
//        apply T17 h; apply T21 h;
//      }
//    }{
//      apply T17 h;
//      apply T21 h;
//    }
//  end;

//type tc_example;
