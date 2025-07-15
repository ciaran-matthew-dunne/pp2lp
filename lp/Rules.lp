require open Logic.U.Set Logic.U.Prop Logic.U.Arrow Logic.U.Inf;
require open pp2lp.Prelude pp2lp.Syntax;

// ----------------------------------------------
// 5.1. Conjunction
// ----------------------------------------------
symbol AND1 [H : El (list prd)] [P Q R : El prd] :
  El (
    ▷ (H ⟝ not Q => R) ⤳
    ▷ (H ⟝ not P => R) ⤳
    ▷ (H ⟝ not (P and Q) => R)
  );

symbol AND2 [H : El (list prd)] [P Q : El prd] :
  El (
    ▷ (H ⟝ P => not Q) ⤳
    ▷ (H ⟝ not (P and Q))
  );

symbol AND2' [H : El (list prd)] [P Q : El prd] :
  El (
    ▷ (H ⟝ P => not Q) ⤳
    ▷ (H ⟝ not (P and Q))
  );

symbol AND3 [H : El (list prd)] [P Q R : El prd] :
  El (
    ▷ (H ⟝ P => (Q => R)) ⤳
    ▷ (H ⟝ (P and Q) => R)
  );

symbol AND4 [H : El (list prd)] [P Q : El prd] :
  El (
    ▷ (H ⟝ Q) ⤳
    ▷ (H ⟝ P) ⤳
    ▷ (H ⟝ (P and Q))
  );

symbol AND5 [H : El (list prd)] [P R A B : El prd] :
  El (
    (A ∈ unfold_conj P) ⇛
    ▷ (H ⟝ fold_conj (replace (A => B) B (unfold_conj P)) => R) ⤳
    ▷ (H ⟝ P => R)
);


// ----------------------------------------------
// 5.2. Disjunction
// ----------------------------------------------
symbol OR1 [H : El (list prd)] [P Q R : El prd] :
  El (
    ▷ (H ⟝ not P => (not Q => R)) ⤳
    ▷ (H ⟝ not (P or Q) => R)
  );

symbol OR2 [H : El (list prd)] [P Q : El prd] :
  El (
    ▷ (H ⟝ not Q) ⤳
    ▷ (H ⟝ not P) ⤳
    ▷ (H ⟝ not (P or Q))
  );

symbol OR3 [H : El (list prd)] [P Q R : El prd] :
  El (
    ▷ (H ⟝ Q => R) ⤳
    ▷ (H ⟝ P => R) ⤳
    ▷ (H ⟝ (P or Q) => R)
  );

symbol OR4 [H : El (list prd)] [P Q : El prd] :
  El (
    ▷ (H ⟝ not P => Q) ⤳
    ▷ (H ⟝ (P or Q))
  );


// ----------------------------------------------
// 5.3. Implication
// ----------------------------------------------
symbol IMP1 [H : El (list prd)] [P Q R : El prd] :
  El (
    ▷ (H ⟝ P => (not Q => R)) ⤳
    ▷ (H ⟝ not (P => Q) => R)
  );

symbol IMP2 [H : El (list prd)] [P Q : El prd] :
  El (
    ▷ (H ⟝ not Q) ⤳
    ▷ (H ⟝ P) ⤳ // This is "H ⊢ P" in the antecedent
    ▷ (H ⟝ not (P => Q))
  );

symbol IMP3 [H : El (list prd)] [P Q R : El prd] :
  El (
    ▷ (H ⟝ Q => R) ⤳
    ▷ (H ⟝ not(P) => R) ⤳
    ▷ (H ⟝ (P => Q) => R)
  );

symbol IMP4 [H : El (list prd)] [P Q : El prd] :
  El (
    ▷ (P ∷ H ⟝ Q) ⤳
    ▷ (H ⟝ P => Q)
  );

symbol IMP5 [H : El (list prd)] [P Q : El prd] :
  El (
    (P ∈ H) ⇛
    ▷ (H ⟝ Q) ⤳
    ▷ (H ⟝ P => Q)
  );

symbol IMP4' [H : El (list prd)] [P Q R S : El prd] :
  El (
    ((P ∷ H ⟝ Q) ⟿ R) ⤳
    ((H ⟝ P => Q) ⟿ (P => R))
  );


// ----------------------------------------------
// 5.4. Equivalence
// ----------------------------------------------
symbol EQV1 [H : El (list prd)] [P Q R : El prd] :
  El (
    ▷ (H ⟝ P => (not Q => R)) ⤳
    ▷ (H ⟝ not P => (Q => R)) ⤳
    ▷ (H ⟝ not (P <=> Q) => R)
  );

symbol EQV2 [H : El (list prd)] [P Q : El prd] :
  El (
    ▷ (H ⟝ P => not Q) ⤳
    ▷ (H ⟝ not Q => P) ⤳
    ▷ (H ⟝ not (P <=> Q))
  );

symbol EQV3 [H : El (list prd)] [P Q R : El prd] :
  El (
    ▷ (H ⟝ P => (Q => R)) ⤳
    ▷ (H ⟝ not P => (not Q => R)) ⤳
    ▷ (H ⟝ (P <=> Q) => R)
  );

symbol EQV4 [H : El (list prd)] [P Q : El prd] :
  El (
    ▷ (H ⟝ P => Q) ⤳
    ▷ (H ⟝ Q => P) ⤳
    ▷ (H ⟝ (P <=> Q))
  );


// ----------------------------------------------
// 5.5. Negation
// ----------------------------------------------
symbol NOT1 [H : El (list prd)] [P R : El prd] :
  El (
    ▷ (H ⟝ P => R) ⤳
    ▷ (H ⟝ not not P => R)
  );

symbol NOT2 [H : El (list prd)] [P : El prd] :
  El (
    ▷ (H ⟝ P) ⤳
    ▷ (H ⟝ not not P)
  );


// ----------------------------------------------
// 5.6. Axioms
// ----------------------------------------------
symbol AXM1 [H : El (list prd)] [P Q : El prd] :
  El (
    (not P ∈ H) ⇛
    ▷ (H ⟝ P => Q)
  );

symbol AXM2 [H : El (list prd)] [P Q : El prd] :
  El (
    (P ∈ H) ⇛
    ▷ (H ⟝ not P => Q)
  );

symbol AXM3 [H : El (list prd)] [P : El prd] :
  El (
    (P ∈ H) ⇛
    ▷ (H ⟝ P)
  );

symbol AXM4 [H : El (list prd)] [P R : El prd] :
  El (
    (R ∈ H) ⇛
    ▷ (H ⟝ P => R)
  );

symbol AXM5 [H : El (list prd)] [P Q R : El prd] :
  El (
    (not Q ∈ H) ⇛
    ▷ (H ⟝ P => (Q => R))
  );

symbol AXM6 [H : El (list prd)] [P Q R : El prd] :
  El (
    (Q ∈ H) ⇛
    ▷ (H ⟝ P => (not Q => R))
  );

symbol AXM7 [H : El (list prd)] [P : El prd] :
  El (
    ▷ (H ⟝ P => P)
  );

symbol AXM8 [H : El (list prd)] [P R : El prd] :
  El (
    (R ∈ unfold_conj P) ⇛
    ▷ (H ⟝ P => R)
  );

symbol AXM9 [H : El (list prd)] [P : El (exp ⤳ prd)] [Q : El prd] [x : El idt] [E : El exp] :
  El (
    (∀1 x (not (VRAI and P (var x))) ∈ H) ⇛
    ▷ (H ⟝ P E => Q)
  );


// ----------------------------------------------
// 5.7. Universal quantification
// ----------------------------------------------
symbol ALL1 [H : El (list prd)] [x y : El idt] [P : El (exp ⤳ exp ⤳ prd)] [R : El prd] :
  El (
    ¬ (x ≣ y) ⇛
    ▷ (H ⟝ (not (∀2 x y (P (var x) (var y)))) => R) ⤳
    ▷ (H ⟝ (not (∀1 x (∀1 y (P (var x) (var y))))) => R)
  );

symbol ALL2 [H : El (list prd)] [x y : El idt] [P : El (exp ⤳ exp ⤳ prd)] :
  El (
    ¬ (x ≣ y) ⇛
    ▷ (H ⟝ (not (∀2 x y (P (var x) (var y))))) ⤳
    ▷ (H ⟝ (not (∀1 x (∀1 y (P (var x) (var y))))))
  );

symbol ALL3 [H : El (list prd)] [x y : El idt] [P : El (exp ⤳ exp ⤳ prd)] [R : El prd] :
  El (
    ¬ (x ≣ y) ⇛
    ▷ (H ⟝ (∀2 x y (P (var x) (var y))) => R) ⤳
    ▷ (H ⟝ (∀1 x (∀1 y (P (var x) (var y)))) => R)
  );

symbol ALL4 [x y : El idt] [H : El (list prd)] [P : El (exp ⤳ exp ⤳ prd)] :
  El (
    ¬ (x ≣ y) ⇛
    ▷ (H ⟝ (∀2 x y (P (var x) (var y)))) ⤳
    ▷ (H ⟝ (∀1 x (∀1 y (P (var x) (var y)))))
  );

symbol ALL5 [H : El (list prd)] [P : El (exp ⤳ prd)] [x : El idt] [R : El prd] :
  El (
    ▷ (H ⟝ ∀1 x (not (P (var x) => R))) ⤳
    ▷ (H ⟝ (not (∀1 x (P (var x)))) => R)
  );

symbol ALL6 [H : El (list prd)] [P : El prd] [xs : El vrb] :
  El (
    ▷ (H ⟝ ! xs P => FAUX) ⤳
    ▷ (H ⟝ not (! xs P))
  );

symbol ALL7 [H : El (list prd)] [P R : El (exp ⤳ prd)] [Q : El prd] [x : El idt]:
  El (
    ((H ⟝ P (var x)) ⟿ R) ⤳
    ▷ (H ⟝ (♢1 x (R (var x))) => Q) ⤳
    ▷ (H ⟝ (∀1 x (P (var x))) => Q)
  );

symbol ALL8 [H : El (list prd)] [P : El prd] [xs : El vrb] :
  El (
    ▷ (H ⟝ P) ⤳
    ▷ (H ⟝ ! xs P)
  );

symbol ALL9 [H : El (list prd)] [T : El (exp ⤳ prd)] [Q : El prd] :
  El (
    ▷ ((! T) ∷ H ⟝ Q) ⤳
    ▷ (H ⟝ ♡ T => Q)
  );

symbol ALL7' [H : El (list prd)] [P Q R S : El prd] :
  El (
    Prf ((H ⟝ P) ⟿ R) ⤳
    Prf ((H ⟝ (`♢ x, R) => Q) ⟿ S) ⤳
    Prf ((H ⟝ (`! x, P) => Q) ⟿ S)
  );

symbol ALL8' [H : El (list prd)] [P Q : El prd] :
  El (
    Prf ((H ⟝ P) ⟿ Q) ⤳
    Prf ((H ⟝ (`! x, P)) ⟿ (`! x, Q))
  );

symbol ALL9' [H : El (list prd)] [P : El (exp ⤳ prd)] [Q R : El prd] :
  El (
    Prf (((! P) ∷ H ⟝ Q) ⟿ R) ⤳
    Prf ((H ⟝ (♡ P) => Q) ⟿ (! P) => R)
  );

// (??) redunant rules due to HOAS
symbol ALL5_1 [H : El (list prd)] [P R : El prd] : TYPE;
symbol ALL7_1 [H : El (list prd)] [P Q R S A : El prd] : TYPE;
symbol ALL7'_1 [H : El (list prd)] [P Q R S A : El prd] : TYPE;
symbol ALL8'_1 [H : El (list prd)] [P Q : El prd] : TYPE;

// ----------------------------------------------
// 5.8. Existential quantification
// ----------------------------------------------

symbol XST1 [x y : El idt] [H : El (list prd)] [P R : El prd] :
  El (
    ▷ (H ⟝ not (`# x, `# y, P) => R) ⤳
    ▷ (H ⟝ not (`# x, `# y, P) => R)
  );

symbol XST2 [x y : El idt] [H : El (list prd)] [P : El prd] :
  El (
    ▷ (H ⟝ not (`# x, `# y, P)) ⤳
    ▷ (H ⟝ not (`# x, `# y, P))
  );

symbol XST3 [x y : El idt] [H : El (list prd)] [P R : El prd] :
  El (
    ▷ (H ⟝ (`# x, `# y, P) => R) ⤳
    ▷ (H ⟝ (`# x, `# y, P) => R)
  );

symbol XST4 [x y : El idt] [H : El (list prd)] [P : El prd] :
  El (
    ▷ (H ⟝ `# x, `# y, P) ⤳
    ▷ (H ⟝ `# x, `# y, P)
  );

symbol XST5 [x : El idt] [H : El (list prd)] [P R : El prd] :
  El (
    ▷ (H ⟝ (`! x, not P) => R) ⤳
    ▷ (H ⟝ not (`# x, P) => R)
  );

symbol XST5_1 [x : El idt] [H : El (list prd)] [P R : El prd] :
  El (
    ▷ (H ⟝ (`! x, P) => R) ⤳
    ▷ (H ⟝ not (`# x, not P) => R)
  );

symbol XST6 [x : El idt] [H : El (list prd)] [P : El prd] :
  El (
    ▷ (H ⟝ `! x, not P) ⤳
    ▷ (H ⟝ not (`# x, P))
  );

symbol XST6_1 [x : El idt] [H : El (list prd)] [P : El prd] :
  El (
    ▷ (H ⟝ `! x, P) ⤳
    ▷ (H ⟝ not (`# x, not P))
  );

symbol XST7 [x : El idt] [H : El (list prd)] [P R Q : El prd] :
  El (
    ▷ (H ⟝ `! x, (P => R)) ⤳
    ▷ (H ⟝ (`# x, P) => R)
  );

symbol XST8 [x y : El idt] [H : El (list prd)] [P R A : El prd] :
  El (
    Prf ((H ⟝ not P) ⟿ R) ⤳
    ▷ (H ⟝ (`! x, R) => VRAI) ⤳
    ▷ (H ⟝ (`# x, P))
  );

// redunant rules.
symbol XST7_1 [x : El idt] [H : El (list prd)] [P R Q : El prd] : TYPE;
symbol XST8_1 [x y : El idt] [H : El (list prd)] [P R A : El prd] : TYPE;

// ----------------------------------------------
// 5.9. Vrai et Faux
// ----------------------------------------------
symbol VR1 [H : El (list prd)] [R : El prd] :
  El (
    ▷ (H ⟝ not VRAI => R)
  );

symbol VR2 [H : El (list prd)] :
  El (
    ▷ (H ⟝ VRAI) ⤳
    ▷ (H ⟝ not VRAI)
  );

symbol VR3 [H : El (list prd)] [R : El prd] :
  El (
    ▷ (H ⟝ R) ⤳
    ▷ (H ⟝ VRAI => R)
  );

symbol VR4 [H : El (list prd)] [R : El prd] :
  El (
    ▷ (H ⟝ VRAI)
  );

symbol FX1 [H : El (list prd)] [R : El prd] :
  El (
    ▷ (H ⟝ R) ⤳
    ▷ (H ⟝ not VRAI => R)
  );

symbol FX2 [H : El (list prd)] [R : El prd] :
  El (
    ▷ (H ⟝ not VRAI)
  );

symbol FX3 [H : El (list prd)] [R : El prd] :
  El (
    ▷ (H ⟝ VRAI => R)
  );


// ----------------------------------------------
// 5.10. STOP rules
// ----------------------------------------------
symbol STOP [H : El (list prd)] [P : El prd] :
  El (
    Prf (¬ (P ≈ FAUX)) ⤳
    ▷ (H ⟝ not P => FAUX) ⤳
    ▷ (H ⟝ P)
  );

symbol STOP' [H : El (list prd)] [P : El prd] :
  El (
    ▷ (H ⟝ P) ⤳
    return P
  );

// ----------------------------------------------
// 5.11 INS rule
// ----------------------------------------------
symbol ⭆ : El (list prd ⤳ prd ⤳ prd);
notation ⭆ infix 5;

rule (nil ⭆ $p) ↪ $p
with (($q ∷ $qs) ⭆ $p) ↪ $q => ($qs ⭆ $p);

symbol INS [H Q : El (list prd)] :
  El (
    ▷ (H ⟝ Q ⭆ FAUX) ⤳
    ▷ (H ⟝ FAUX)
  );

// ----------------------------------------------
// 5.12. Normalization rules
// ----------------------------------------------
symbol NRM1 [H : El (list prd)] [P S : El prd] [xs : El vrb] :
  El (
    ▷ (H ⟝ P => S) ⤳
    ▷ (H ⟝ (♢ xs P) => S)
  );

symbol NRM2 [H : El (list prd)] [P Q S : El prd] :
  El (
    ▷ (H ⟝ P => (`♢ x, Q) => S) ⤳
    ▷ (H ⟝ `♢ x, (P => Q) => S)
  );

symbol NRM3 [H : El (list prd)] [P Q S : El prd] :
  El (
    Prf (¬ (Q ≈ FAUX)) ⤳
    ▷ (H ⟝ (Q => S) and ((`! x, not P) => S)) ⤳
    ▷ (H ⟝ `♢ x, (P => Q) => S)
  );

symbol NRM4 [H : El (list prd)] [P Q R S : El prd] :
  El (
    ▷ (H ⟝ (Q => `♢ x, (P => R)) => S) ⤳
    ▷ (H ⟝ `♢ x, (P => (Q => R)) => S)
  );

symbol NRM5 [H : El (list prd)] [P Q R S : El prd] :
  El (
    ▷ (H ⟝ `♢ x, (P and Q => R) => S) ⤳
    ▷ (H ⟝ `♢ x, (P => (Q => R)) => S)
  );

symbol NRM6 [H : El (list prd)] [P Q R S : El prd] :
  El (
    ▷ (H ⟝ `♢ x, (R => P) => (`♢ x, (R => Q) => S)) ⤳
    ▷ (H ⟝ `♢ x, (R => P and Q) => S)
  );

symbol NRM7 [H : El (list prd)] [P Q S : El prd] :
  El (
    ▷ (H ⟝ (`♢ x, P) => ((`♢ x, Q) => S)) ⤳
    ▷ (H ⟝ (`♢ x, (P and Q) => S))
  );

symbol NRM8 [H : El (list prd)] [Q S : El prd] :
  El (
    ▷ (H ⟝ (`♢ x, `♢ y, Q) => S) ⤳
    ▷ (H ⟝ (`♢ x, `! y, Q) => S)
  );

symbol NRM9 [H : El (list prd)] [P Q S : El prd] :
  El (
    ▷ (H ⟝ `♢ x, `♢ y, (P => Q) => S) ⤳
    ▷ (H ⟝ `♢ x, (P => `! y, Q) => S)
  );

symbol NRM10 [H : El (list prd)] [P Q R : El prd] :
  El (
    ▷ (H ⟝ `♡ x, not (P and Q) => R) ⤳
    ▷ (H ⟝ `♢ x, (P and Q => FAUX) => R)
  );

symbol NRM11 [H : El (list prd)] [P R : El prd] :
  El (
    ▷ (H ⟝ `♡ x, not (VRAI and P) => R) ⤳
    ▷ (H ⟝ `♢ x, (P => FAUX) => R)
  );

symbol NRM12 [H : El (list prd)] [P Q R : El prd] :
  El (
    ▷ (H ⟝ `♡ x, not (P and Q) => R) ⤳
    ▷ (H ⟝ `♢ x, (P => not Q) => R)
  );

symbol NRM13 [H : El (list prd)] [P Q R : El prd] :
  El (
    ▷ (H ⟝ `♡ x, not (P and not Q) => R) ⤳
    ▷ (H ⟝ `♢ x, (P => Q) => R)
  );

symbol NRM14 [H : El (list prd)] [P R : El prd] :
  El (
    ▷ (H ⟝ `♡ x, not (VRAI and P) => R) ⤳
    ▷ (H ⟝ (`♢ x, not P) => R)
  );

symbol NRM15 [H : El (list prd)] [P R : El prd] :
  El (
    ▷ (H ⟝ `♡ x, not (VRAI and not P) => R) ⤳
    ▷ (H ⟝ (`♢ x, P) => R)
  );

symbol NRM16 [H : El (list prd)] [P : El (exp ⤳ prd)] [Q : El prd] :
  El (
    Prf (elem (! P) H) ⤳
    ▷ (H ⟝ Q) ⤳
    ▷ (H ⟝ (♡ P) => Q)
  );

// hopefully higher-order unification sorts this out
symbol NRM17 [H : El (list prd)] [P : El (exp ⤳ prd)] [Q : El prd] [E : El exp] :
  El (
    Prf (elem (`! x, not (VRAI and P x)) H) ⤳
    ▷ (H ⟝ (`♡ y, not (VRAI and not (P E))) => Q)
  );

symbol NRM18 [H : El (list prd)] [P : El (exp ⤳ prd)] [R Q : El prd] [E : El exp] :
  El (
    Prf (elem (`! x, not (VRAI and not (P x))) H) ⤳
    Prf (P E ≈ R) ⤳
    ▷ (H ⟝ (`♡ y, not (VRAI and R)) => Q)
  );

symbol NRM19 [H : El (list prd)] [R : El (exp ⤳ prd)] [P Q : El prd] [E : El exp] :
  El (
    Prf (elem P H) ⤳
    Prf ((R E) ≈ P) ⤳
    ▷ (H ⟝ (`♡ x, not (VRAI and (R x))) => Q)
  );

symbol NRM20 [H : El (list prd)] [P : El (exp ⤳ prd)] [Q : El prd] [E : El exp] :
  El (
    ▷ (H ⟝ `♡ y, not (P E) => Q) ⤳
    ▷ (H ⟝ `♡ x, `♡ y, not (P x and (E = x)) => Q)
  );

symbol NRM21 [H : El (list prd)] [P : El (exp ⤳ prd)] [Q : El prd] [E : El exp] :
  El (
    ▷ (H ⟝ `♡ y, not (P E) => Q) ⤳
    ▷ (H ⟝ `♡ x, `♡ y, not (P x and (x = E)) => Q)
  );

symbol NRM22 [H : El (list prd)] [P : El (exp ⤳ prd)] [Q : El prd] [E : El exp] :
  El (
    ▷ (H ⟝ not (P E) => Q) ⤳
    ▷ (H ⟝ `♡ x, not (P x and (x = E)) => Q)
  );

symbol NRM23 [H : El (list prd)] [P : El (exp ⤳ prd)] [Q : El prd] [E : El exp] :
  El (
    ▷ (H ⟝ not (P E) => Q) ⤳
    ▷ (H ⟝ `♡ x, not (P x and (E = x)) => Q)
  );

sequential symbol NRM24_aux : El (prd ⤳ bool);

rule NRM24_aux ($A and $B) ↪ ⊥
with NRM24_aux  _          ↪ ⊥;

symbol NRM24 [H : El (list prd)] [P Q : El prd] :
  El (
    Prf (NRM24_aux P) ⤳
    ▷ (H ⟝ `♡ x, not (VRAI and P) => Q) ⤳
    ▷ (H ⟝ `♡ x, not P => Q)
  );

symbol NRM25 [H : El (list prd)] [P : El prd] :
  El (
    ▷ (H ⟝ P) ⤳
    ▷ (H ⟝ `♡ x, P)
  );

symbol NRM26 [H : El (list prd)] [P : El (exp ⤳ prd)] :
  El (
    ▷ (H ⟝ `♡ x, P x) ⤳
    ▷ (H ⟝ `♡ x, `♡ y, P x)
  );

// ---- not yet implemented, possibly requires manipulation of variables? ------
symbol NRM27 [H : El (list prd)] [P Q : El prd] : TYPE;

symbol NRM29 [H : El (list prd)] [P Q S R : El prd] [a b : El exp] : TYPE;

symbol NRM29_1 [H : El (list prd)] [P Q S R : El prd] [a b : El exp] : TYPE;
// -----------------------------------------------------------------------------

symbol NRM30 [H : El (list prd)] [P' : El (exp ⤳ prd)] [S R : El prd] [a b x : El exp] :
  El (
    Prf (elem ((a + x) ≤ 𝟎) (to_list (P' x))) ⤳
    Prf (elem ((b - x) ≤ 𝟎) (to_list (P' x))) ⤳
    Prf (ev (a + b = 𝟎)) ⤳
    ▷ (H ⟝ not (P' b) => R) ⤳
    ▷ (H ⟝ `♡ x, not (P' x) => R)
  );

symbol NRM30_1 [H : El (list prd)] [P' : El (exp ⤳ prd)] [S R : El prd] [a b x : El exp] :
  El (
    Prf (elem ((x + a) ≤ 𝟎)   (to_list (P' x))) ⤳
    Prf (elem ((⨪ x + b) ≤ 𝟎) (to_list (P' x))) ⤳
    Prf (ev (a + b = 𝟎)) ⤳
    ▷ (H ⟝ not (P' b) => R) ⤳
    ▷ (H ⟝ `♡ x, not (P' x) => R)
  );

// redunant rules??
symbol NRM8_1 : TYPE;
symbol NRM9_1 : TYPE;


// ----------------------------------------------
// 5.13. Rules for equality
// ----------------------------------------------
symbol EVR1 [H : El (list prd)] [P : El prd] [E : El exp] :
  El (
    ▷ (H ⟝ not (E = E) => P)
  );

symbol EVR11 [H : El (list prd)] [P : El prd] [n m : El exp] :
  El (
    Prf (ev (n != m)) ⤳
    Prf (n ∈ ℕ) ⤳
    Prf (m ∈ ℕ) ⤳
    ▷ (H ⟝ (n = m) => P)
  );

symbol EVR2 [H : El (list prd)] [E : El exp] :
  El (
    ▷ (H ⟝ FAUX) ⤳
    ▷ (H ⟝ not (E = E))
  );

symbol EVR3 [H : El (list prd)] [P : El prd] [E : El exp] :
  El (
    ▷ (H ⟝ P) ⤳
    ▷ (H ⟝ (E = E) => P)
  );

symbol EVR4 [H : El (list prd)] [E : El exp] :
  El (
    ▷ (H ⟝ (E = E))
  );

symbol EAXM1 [H : El (list prd)] [E F : El exp] [P : El prd] :
  El (
    Prf (elem (not (F = E)) H) ⤳
    ▷ (H ⟝ (E = F) => P)
  );

symbol EAXM2 [H : El (list prd)] [E F : El exp] [P : El prd] :
  El (
    Prf (elem (F = E) H) ⤳
    ▷ (H ⟝ not (E = F) => P)
  );

symbol EAXM3_1 [H : El (list prd)] [E F : El exp] [P : El prd] :
  El (
    Prf (elem (F = E) H) ⤳
    ▷ (H ⟝ (E = F))
  );

symbol EAXM3_2 [H : El (list prd)] [E F : El exp] [P : El prd] :
  El (
    Prf (elem (not (F = E)) H) ⤳
    ▷ (H ⟝ not (E = F))
  );

symbol EIMP5_1 [H : El (list prd)] [E F : El exp] [P : El prd] :
  El (
    Prf (elem (not (F = E)) H) ⤳
    ▷ (H ⟝ P) ⤳
    ▷ (H ⟝ not (E = F) => P)
  );

symbol EIMP5_2 [H : El (list prd)] [E F : El exp] [P : El prd] :
  El (
    Prf (elem (F = E) H) ⤳
    ▷ (H ⟝ P) ⤳
    ▷ (H ⟝ (E = F) => P)
  );

symbol EQC1 [H : El (list prd)] [a b c d : El exp] [P : El prd] :
  El (
    ▷ (H ⟝ not (a = c) or not (b = d) => P) ⤳
    ▷ (H ⟝ not (opair a b = opair c d) => P)
  );

symbol EQC2 [H : El (list prd)] [a b c d : El exp] [P : El prd] :
  El (
    ▷ (H ⟝ (a = c) and (b = d) => P) ⤳
    ▷ (H ⟝  (opair a b = opair c d) => P)
  );

symbol EQS1 [H : El (list prd)] [E F : El exp] [P : El prd] :
  El (
    ▷ (H ⟝ (E = F) => P) ⤳
    ▷ (H ⟝ (eql_set E F) => P)
  );

symbol EQS2 [H : El (list prd)] [E F : El exp] [P : El prd] :
  El (
    ▷ (H ⟝ FAUX => P) ⤳
    ▷ (H ⟝ not (eql_set E F) => P)
  );

symbol EAXM9_1 [H : El (list prd)] [p q : El (exp ⤳ exp)] [E : El exp] [Q : El prd] :
  El (
    Prf (elem (`! x, not (VRAI and (p x = q x))) H) ⤳
    ▷ (H ⟝ ((p E) = (q E)) => Q)
  );

symbol EAXM9_2 [H : El (list prd)] [p q : El (exp ⤳ exp)] [E : El exp] [Q : El prd] :
  El (
    Prf (elem (`! x, not (VRAI and not (p x = q x))) H) ⤳
    ▷ (H ⟝ not ((p E) = (q E)) => Q)
  );

symbol OPR1 [H : El (list prd)] [P : El prd] [x : El idt] [E : El exp] :
  El (
    ▷ (H ⟝ P) ⤳
    ▷ (H ⟝ (var x = E) => P)
  );

symbol OPR2 [H : El (list prd)] [P : El (exp ⤳ prd)] [x E : El exp] :
  El (
    ▷ (H ⟝ P E) ⤳
    ▷ (H ⟝ (E = x) => P x)
  );

symbol ECTR1 [H : El (list prd)] [P : El prd] [Q : El (exp ⤳ prd)] [E F : El exp] :
  El (
    Prf (elem (not (Q E)) H) ⤳
    Prf (elem (Q F) H) ⤳
    ▷ (H ⟝ (E = F) => P)
  );

symbol ECTR2 [H : El (list prd)] [P : El prd] [Q : El (exp ⤳ prd)] [E F : El exp] :
  El (
    Prf (elem (not (Q E)) H) ⤳
    Prf (elem (Q F) H) ⤳
    ▷ (H ⟝ (F = E) => P)
  );

symbol ECTR3 [H : El (list prd)] [Q : El prd] [P : El (exp ⤳ prd)] [E F : El exp] :
  El (
    Prf (elem (E = F) H) ⤳
    Prf (elem (P F) H) ⤳
    ▷ (H ⟝ not (P E) => Q)
  );

symbol ECTR4 [H : El (list prd)] [Q : El prd] [P : El (exp ⤳ prd)] [E F : El exp] :
  El (
    Prf (elem (F = E) H) ⤳
    Prf (elem (P F) H) ⤳
    ▷ (H ⟝ not (P E) => Q)
  );

symbol ECTR5 [H : El (list prd)] [Q : El prd] [P : El (exp ⤳ prd)] [E F : El exp] :
  El (
    Prf (elem (E = F) H) ⤳
    Prf (elem (not (P F)) H) ⤳
    ▷ (H ⟝ P E => Q)
  );

symbol ECTR6 [H : El (list prd)] [Q : El prd] [P : El (exp ⤳ prd)] [E F : El exp] :
  El (
    Prf (elem (F = E) H) ⤳
    Prf (elem (not (P F)) H) ⤳
    ▷ (H ⟝ P E => Q)
  );


// ----------------------------------------------
// 5.14. Rules for arithmetic
// ----------------------------------------------
symbol AR1 [H : El (list prd)] [E : El exp] [R : El prd] :
  El (
    ▷ (H ⟝ R) ⤳
    ▷ (H ⟝ (E ≤ E) => R)
  );

symbol AR2 [a b : El exp] [H : El (list prd)] [R : El prd] :
  El (
    Prf (ev (a > b)) ⤳
    ▷ (H ⟝ a ≤ b => R)
  );

symbol AR3 [a : El exp] [H : El (list prd)] [R : El prd] :
  El (
    ▷ (H ⟝ ((𝟏 - a) ≤ 𝟎) => R) ⤳
    ▷ (H ⟝ not (a ≤ 𝟎) => R)
  );

symbol AR4 [E F : El exp] [H : El (list prd)] [R : El prd] :
  El (
    Prf (elem (F ≤ 𝟎) H) ⤳
    Prf (ev ((E + F) > 𝟎)) ⤳
    ▷ (H ⟝ E ≤ 𝟎 => R)
  );

symbol AR5 [a : El exp] [H : El (list prd)] [R : El prd] :
  El (
    Prf (elem (a ≪ 𝟎) H) ⤳
    ▷ (H ⟝ (a = 𝟎 => (⨪ a ≤ 𝟎 => R))) ⤳
    ▷ (H ⟝ ⨪ a ≤ 𝟎 => R)
  );

symbol AR6 [a : El exp] [H : El (list prd)] [R : El prd] :
  El (
    Prf (elem (⨪ a ≪ 𝟎) H) ⤳
    ▷ (H ⟝ (a = 𝟎 => (a ≤ 𝟎 => R))) ⤳
    ▷ (H ⟝ a ≤ 𝟎 => R)
  );

symbol AR7 [a b c : El exp] [H : El (list prd)] [R : El prd] :
  El (
    Prf (elem ((c + b) ≪ 𝟎) H) ⤳
    Prf (ev ((a + c) = 𝟎)) ⤳
    ▷ (H ⟝ (a = b) => ((a - b) ≤ 𝟎) => R) ⤳
    ▷ (H ⟝ ((a - b) ≤ 𝟎) => R)
  );

symbol AR8 [a b c : El exp] [H : El (list prd)] [R : El prd] :
  El (
    Prf (elem ((a - b) ≪ 𝟎) H) ⤳
    Prf (ev ((a + c) = 𝟎)) ⤳
    ▷ (H ⟝ (a = b) => ((c + b) ≤ 𝟎) => R) ⤳
    ▷ (H ⟝ ((c + b) ≤ 𝟎) => R)
  );

symbol AR9 [E F : El exp] [H : El (list prd)] [R : El prd] :
  El (
    Prf (ev E ≈ F) ⤳
    ▷ (H ⟝ (F ≤ 𝟎) => R) ⤳
    ▷ (H ⟝ (E ≤ 𝟎) => R)
  );

symbol AR10 [H : El (list prd)] [P Q R : El prd] :
  El (
    Prf (ev P ≈ Q) ⤳
    ▷ (H ⟝ Q => R) ⤳
    ▷ (H ⟝ P => R)
  );

symbol AR11 [x : El exp] [H : El (list prd)] [P : El prd] :
  El (
    ▷ (H ⟝ not (x ≤ x) => P)
  );

symbol AR12 [a b : El exp] [H : El (list prd)] [P : El prd] :
  El (
    ▷ ((a ≤ b) ∷ H ⟝ (a ≤ b) => P)
  );


// ----------------------------------------------
// 5.15 Booleans
// ----------------------------------------------
// in contrast to `VRAI` and `FAUX` in `VRFX` (both of type `prd`),
// the rules in this file operate on boolean values of type `exp`.
// ----------------------------------------------
symbol FALSE : El exp;
symbol TRUE : El exp;

symbol BOOL1_1 [H : El (list prd)] [P : El prd] [v : El exp] :
  El (
    ▷ ((not (v = FALSE)) ∷ (v = TRUE) ∷ H ⟝ P) ⤳
    ▷ (H ⟝ (v = TRUE) => P)
  );

symbol BOOL1_2 [H : El (list prd)] [P : El prd] [v : El exp] :
  El (
    ▷ ((v = FALSE) ∷ (not (v = TRUE)) ∷ H ⟝ P) ⤳
    ▷ (H ⟝ (v = FALSE) => P)
  );

symbol BOOL2_1 [H : El (list prd)] [P : El prd] [v : El exp] :
  El (
    ▷ (H ⟝ (v = TRUE) => P) ⤳
    ▷ (H ⟝ (TRUE = v) => P)
  );

symbol BOOL2_2 [H : El (list prd)] [P : El prd] [v : El exp] :
  El (
    ▷ (H ⟝ (v = FALSE) => P) ⤳
    ▷ (H ⟝ (FALSE = v) => P)
  );

symbol BOOL3_1 [H : El (list prd)] [P : El prd] [v : El exp] :
  El (
    ▷ (H ⟝ (v = FALSE) => P) ⤳
    ▷ (H ⟝ not (v = TRUE) => P)
  );

symbol BOOL3_2 [H : El (list prd)] [P : El prd] [v : El exp] :
  El (
    ▷ (H ⟝ (v = TRUE) => P) ⤳
    ▷ (H ⟝ not (v = FALSE) => P)
  );

symbol BOOL4_1 [H : El (list prd)] [P : El prd] [v : El exp] :
  El (
    ▷ (H ⟝ (v = FALSE) => P) ⤳
    ▷ (H ⟝ not (TRUE = v) => P)
  );

symbol BOOL4_2 [H : El (list prd)] [P : El prd] [v : El exp] :
  El (
    ▷ (H ⟝ (v = TRUE) => P) ⤳
    ▷ (H ⟝ not (FALSE = v) => P)
  );

symbol BOOL5_1 [H : El (list prd)] [P : El prd] [v : El exp] :
  El (
    ▷ (H ⟝ (TRUE = FALSE) => P)
  );

symbol BOOL5_2 [H : El (list prd)] [P : El prd] [v : El exp] :
  El (
    ▷ (H ⟝ (FALSE = TRUE) => P)
  );
