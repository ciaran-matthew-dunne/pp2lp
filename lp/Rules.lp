require open pp2lp.Syntax;

// ----------------------------------------------
// 5.1. Conjunction
// ----------------------------------------------
symbol AND1 [H : El (list prd)] [P Q R : El prd] :
  ▷ (H ⟝ not Q => R) →
  ▷ (H ⟝ not P => R) →
  ▷ (H ⟝ not (P and Q) => R);

symbol AND2 [H : El (list prd)] [P Q : El prd] :
  ▷ (H ⟝ P => not Q) →
  ▷ (H ⟝ not (P and Q));

symbol AND2_1 [H : El (list prd)] [P Q : El prd] :
  Res (H ⟝ P => not Q) →
  Res (H ⟝ not (P and Q))
≔
  λ ρ, result (obtain ρ);

symbol AND3 [H : El (list prd)] [P Q R : El prd] :
  ▷ (H ⟝ P => (Q => R)) →
  ▷ (H ⟝ (P and Q) => R);

symbol AND4 [H : El (list prd)] [P Q : El prd] :
  ▷ (H ⟝ Q) →
  ▷ (H ⟝ P) →
  ▷ (H ⟝ (P and Q));

symbol AND5 [H : El (list prd)] [P R A B : El prd] :
  ✓ (elem_conj A P) (H ⟝ repl_conj (A => B) B P => R) →
  ▷ (H ⟝ P => R);
// ----------------------------------------------
// 5.2. Disjunction
// ----------------------------------------------
symbol OR1 [H : El (list prd)] [P Q R : El prd] :
  ▷ (H ⟝ not P => (not Q => R)) →
  ▷ (H ⟝ not (P or Q) => R);

symbol OR2 [H : El (list prd)] [P Q : El prd] :
  ▷ (H ⟝ not Q) →
  ▷ (H ⟝ not P) →
  ▷ (H ⟝ not (P or Q));

symbol OR3 [H : El (list prd)] [P Q R : El prd] :
  ▷ (H ⟝ Q => R) →
  ▷ (H ⟝ P => R) →
  ▷ (H ⟝ (P or Q) => R);

symbol OR4 [H : El (list prd)] [P Q : El prd] :
  ▷ (H ⟝ (not P) => Q) →
  ▷ (H ⟝ (P or Q));

// ----------------------------------------------
// 5.3. Implication
// ----------------------------------------------
symbol IMP1 [H : El (list prd)] [P Q R : El prd] :
  ▷ (H ⟝ P => (not Q => R)) →
  ▷ (H ⟝ not (P => Q) => R);

symbol IMP2 [H : El (list prd)] [P Q : El prd] :
  ▷ (H ⟝ not Q) →
  ▷ (H ⟝ P) →
  ▷ (H ⟝ not (P => Q));

symbol IMP3 [H : El (list prd)] [P Q R : El prd] :
  ▷ (H ⟝ Q => R) →
  ▷ (H ⟝ not(P) => R) →
  ▷ (H ⟝ (P => Q) => R);

symbol IMP4 [H : El (list prd)] [P Q : El prd] :
  ▷ (cons P H ⟝ Q) →
  ▷ (H ⟝ P => Q);

symbol IMP5 [H : El (list prd)] [P Q : El prd] :
  ✓ (P ⋿ H) (H ⟝ Q) →
  ▷ (H ⟝ P => Q);

symbol IMP4_1 [H : El (list prd)] [P Q : El prd] :
  Res (cons P H ⟝ Q) →
  Res (H ⟝ P => Q)
≔
  (λ ρ, result (P => obtain ρ));

// ----------------------------------------------
// 5.4. Equivalence
// ----------------------------------------------
symbol EQV1 [H : El (list prd)] [P Q R : El prd] :
  ▷ (H ⟝ P => (not Q => R)) →
  ▷ (H ⟝ not P => (Q => R)) →
  ▷ (H ⟝ not (P <=> Q) => R);

symbol EQV2 [H : El (list prd)] [P Q : El prd] :
  ▷ (H ⟝ P => not Q) →
  ▷ (H ⟝ not Q => P) →
  ▷ (H ⟝ not (P <=> Q));

symbol EQV3 [H : El (list prd)] [P Q R : El prd] :
  ▷ (H ⟝ P => (Q => R)) →
  ▷ (H ⟝ not P => (not Q => R)) →
  ▷ (H ⟝ (P <=> Q) => R);

symbol EQV4 [H : El (list prd)] [P Q : El prd] :
  ▷ (H ⟝ P => Q) →
  ▷ (H ⟝ Q => P) →
  ▷ (H ⟝ (P <=> Q));

// ----------------------------------------------
// 5.5. Negation
// ----------------------------------------------
symbol NOT1 [H : El (list prd)] [P R : El prd] :
  ▷ (H ⟝ P => R) →
  ▷ (H ⟝ not not P => R);

symbol NOT2 [H : El (list prd)] [P : El prd] :
  ▷ (H ⟝ P) →
  ▷ (H ⟝ not not P);

// ----------------------------------------------
// 5.6. Axioms
// ----------------------------------------------
symbol AXM1 [H : El (list prd)] [P Q : El prd] :
  ✓ (not P ⋿ H) (H ⟝ P => Q);

symbol AXM2 [H : El (list prd)] [P Q : El prd] :
  ✓ (P ⋿ H) (H ⟝ not P => Q);

symbol AXM3 [H : El (list prd)] [P : El prd] :
  ✓ (P ⋿ H) (H ⟝ P);

symbol AXM4 [H : El (list prd)] [P R : El prd] :
  ✓ (R ⋿ H) (H ⟝ P => R);

symbol AXM5 [H : El (list prd)] [P Q R : El prd] :
  ✓ (not Q ⋿ H) (H ⟝ P => (Q => R));

symbol AXM6 [H : El (list prd)] [P Q R : El prd] :
  ✓ (Q ⋿ H) (H ⟝ P => (not Q => R));

symbol AXM7 [H : El (list prd)] [P : El prd] :
  ▷ (H ⟝ P => P);

symbol AXM8 [H : El (list prd)] [P R : El prd] :
  ✓ (elem_conj P R) (H ⟝ P => R);

// probably broken. need to handle side condition.
// 'given E such that [x := E] P = R'
symbol AXM9 [H : El (list prd)] [P Q R : El prd]
  [xs : El vrb] [es : El (list exp)]
:
  ✓ (
      (! xs (not (VRAI and P)) ⋿ H)
    &&
      (multisubst xs es P == R)
    )
    (H ⟝ R => Q);

// ----------------------------------------------
// 5.7. Universal quantification
// ----------------------------------------------
symbol ALL1 [H : El (list prd)] [x y : El idt] [P R : El prd] :
  ✓ (x !== y) (H ⟝ (not (! (x ⨾ y) P)) => R) →
  ▷ (H ⟝ (not (! (x ⋅) (! (y ⋅) P))) => R);

symbol ALL2 [H : El (list prd)] [x y : El idt] [P : El prd] :
  ✓ (x !== y) (H ⟝ not (! (x ⨾ y) P)) →
  ▷ (H ⟝ not (! (x ⋅) (! (y ⋅) P)));

symbol ALL3 [H : El (list prd)] [x y : El idt] [P R : El prd] :
  ✓ (x !== y) (H ⟝ (! (x ⨾ y) P) => R) →
  ▷ (H ⟝ (! (x ⋅) (! (y ⋅) P)) => R);

symbol ALL4 [x y : El idt] [H : El (list prd)] [P : El prd] :
  ✓ (x !== y) (H ⟝ ! (x ⨾ y) P) →
  ▷ (H ⟝ ! (x ⋅) (! (y ⋅) P));

symbol ALL5 [H : El (list prd)] [P R : El prd] [xs : El vrb] :
  ▷ (H ⟝ ! (xs) (not P => R)) →
  ▷ (H ⟝ (not (! (xs) P)) => R);

symbol ALL6 [H : El (list prd)] [P : El prd] [xs : El vrb] :
  ▷ (H ⟝ ! xs P => FAUX) →
  ▷ (H ⟝ not (! xs P));

symbol ALL7_ONE [H : El (list prd)] [P Q : El prd] [x : El idt] :
  Π R : Res (H ⟝ P),
    //✓ (free x P)
    ▷ (H ⟝ (♢ (x ⋅) R) => Q) →
    ▷ (H ⟝ (! (x ⋅) P) => Q);

symbol ALL7 [H : El (list prd)] [P Q : El prd] [xs : El vrb] :
  Π R : Res (H ⟝ P),
    ✓ (foreach (λ x, foreach (λ p, !! (free x p)) H) xs)
      (H ⟝ (♢ xs R) => Q) →
    ▷ (H ⟝ (! xs P) => Q);

symbol ALL8 [H : El (list prd)] [P : El prd] [xs : El vrb] :
  ▷ (H ⟝ P) →
  ▷ (H ⟝ ! xs P);

symbol ALL9 [H : El (list prd)] [T Q : El prd] [xs : El vrb] :
  ▷ (cons (! xs T) H ⟝ Q) →
  ▷ (H ⟝ (♡ xs T) => Q);

symbol ALL7_1 [H : El (list prd)] [P Q R S : El prd] [x : El idt] :
  Π R : Res (H ⟝ P),
  Res (H ⟝ (♢ (x ⋅) R) => Q) →
  Res (H ⟝ (! (x ⋅) P) => Q)
≔
  (λ _ ρ, result (obtain ρ));

symbol ALL8_1 [H : El (list prd)] [P : El prd] [x : El idt] :
  Res (H ⟝ P) →
  Res (H ⟝ (! (x ⋅) P))
≔
  (λ ρ, result (! (x ⋅) (obtain ρ)));

symbol ALL9_1 [H : El (list prd)] [P Q R : El prd] [x : El idt] :
  Res (cons (! (x ⋅) P) H ⟝ Q) →
  Res (H ⟝ (♡ (x ⋅) P) => Q)
≔
  (λ ρ, result ((! (x ⋅) P) => (obtain ρ)));

// ----------------------------------------------
// 5.8. Existential quantification
// ----------------------------------------------
symbol XST1 [x y : El idt] [H : El (list prd)] [P R : El prd] :
  ▷ (H ⟝ not (# (x ⨾ y) P) => R) →
  ▷ (H ⟝ not (# (x ⋅) (# (y ⋅) P)) => R);

symbol XST2 [x y : El idt] [H : El (list prd)] [P : El prd] :
  ▷ (H ⟝ not (# (x ⨾ y) P)) →
  ▷ (H ⟝ not (# (x ⋅) (# (y ⋅) P)));

symbol XST3 [x y : El idt] [H : El (list prd)] [P R : El prd] :
  ▷ (H ⟝ (# (x ⨾ y) P) => R) →
  ▷ (H ⟝ (# (x ⋅) (# (y ⋅) P)) => R);

symbol XST4 [x y : El idt] [H : El (list prd)] [P : El prd] :
  ▷ (H ⟝ # (x ⨾ y) P) →
  ▷ (H ⟝ # (x ⋅) (# (y ⋅) P));

symbol XST5 [xs : El vrb] [H : El (list prd)] [P R : El prd] :
  ▷ (H ⟝ (! xs (not P)) => R) →
  ▷ (H ⟝ not (# xs P) => R);

symbol XST51 [x : El idt] [H : El (list prd)] [P R : El prd] :
  ▷ (H ⟝ (! (x ⋅) P) => R) →
  ▷ (H ⟝ (not (# (x ⋅) (not P))) => R);

symbol XST6 [x : El idt] [H : El (list prd)] [P : El prd] :
  ▷ (H ⟝ ! (x ⋅) (not P)) →
  ▷ (H ⟝ not (# (x ⋅) P));

symbol XST61 [x : El idt] [H : El (list prd)] [P : El prd] :
  ▷ (H ⟝ ! (x ⋅) P) →
  ▷ (H ⟝ not (# (x ⋅) (not P)));

symbol XST7 [x : El idt] [H : El (list prd)] [P R : El prd] :
  ✓ (!! (free x R)) (H ⟝ ! (x ⋅) (P => R)) →
  ▷ (H ⟝ (# (x ⋅) P) => R);

symbol XST7_1 [x : El idt] [H : El (list prd)] [P R : El prd] :
  Res ((H ⟝ ! (x ⋅) (P => R))) →
  Res (H ⟝ (# (x ⋅) P) => R)
≔
  (λ ρ, result (obtain ρ));


symbol XST8 [x y : El idt] [H : El (list prd)] [P : El prd] :
  Π R : Res (H ⟝ not P),
  ▷ (H ⟝ (! (x ⋅) R) => FAUX) →
  ▷ (H ⟝ (# (x ⋅) P));

// redundant rules.
symbol XST8_1 [x y : El idt] [H : El (list prd)] [P R A : El prd] : TYPE;

// ----------------------------------------------
// 5.9. Vrai et Faux
// ----------------------------------------------
symbol VR1 [H : El (list prd)] [R : El prd] :
  ▷ (H ⟝ not VRAI => R);

symbol VR2 [H : El (list prd)] :
  ▷ (H ⟝ FAUX) →
  ▷ (H ⟝ not VRAI);

symbol VR3 [H : El (list prd)] [R : El prd] :
  ▷ (H ⟝ R) →
  ▷ (H ⟝ VRAI => R);

symbol VR3_1 [H : El (list prd)] [R : El prd] :
  Res (H ⟝ R) →
  Res (H ⟝ VRAI => R)
≔
  λ ρ, result (obtain ρ);

symbol VR4 [H : El (list prd)] [R : El prd] :
  ▷ (H ⟝ VRAI);

symbol FX1 [H : El (list prd)] [R : El prd] :
  ▷ (H ⟝ R) →
  ▷ (H ⟝ not FAUX => R);

symbol FX2 [H : El (list prd)] [R : El prd] :
  ▷ (H ⟝ not FAUX);

symbol FX3 [H : El (list prd)] [R : El prd] :
  ▷ (H ⟝ FAUX => R);

// ----------------------------------------------
// 5.10. STOP rules
// ----------------------------------------------
symbol STOP [H : El (list prd)] [P : El prd] :
  ✓ (!! (P == FAUX)) (H ⟝ not P => FAUX) →
  ▷ (H ⟝ P);

symbol STOP_1 [H : El (list prd)] [P : El prd] :
  Res (H ⟝ P)
≔
  result P;

// ----------------------------------------------
// 5.11 INS rule
// ----------------------------------------------
symbol ⭆ : El (list prd ⤳ prd ⤳ prd);
notation ⭆ infix 5;

rule (nil ⭆ $p) ↪ $p
with ((cons $q $qs) ⭆ $p) ↪ $q => ($qs ⭆ $p);

symbol INS [H Q : El (list prd)] :
  ▷ (H ⟝ Q ⭆ FAUX) →
  ▷ (H ⟝ FAUX);

// ----------------------------------------------
// 5.12. Normalization rules
// ----------------------------------------------
symbol NRM1 [H : El (list prd)] [P S : El prd] [xs : El vrb] :
  ✓ (foreach (λ x, !! (free x P)) xs) (H ⟝ P => S) →
  ▷ (H ⟝ (♢ xs P) => S);

symbol NRM2 [H : El (list prd)] [P Q S : El prd] [x : El idt] :
  ✓ (!! (free x P)) (H ⟝ (P => (♢ (x ⋅) Q)) => S) →
  ▷ (H ⟝ ♢ (x ⋅) ((P => Q) => S));

symbol NRM3 [H : El (list prd)] [P Q S : El prd] [x : El idt]:
  ✓ (!! (free x Q) && (Q !== FAUX)) (H ⟝ (Q => S) and ((! (x ⋅) (not P)) => S)) →
  ▷ (H ⟝ ♢ (x ⋅) ((P => Q) => S));

symbol NRM4 [H : El (list prd)] [P Q R S : El prd] [x : El idt] :
  ▷ (H ⟝ (Q => ♢ (x ⋅) (P => R)) => S) →
  ▷ (H ⟝ ♢ (x ⋅) (P => (Q => R)) => S);

symbol NRM5 [H : El (list prd)] [P Q R S : El prd] [x : El idt] :
  ▷ (H ⟝ ♢ (x ⋅) (P and Q => R) => S) →
  ▷ (H ⟝ ♢ (x ⋅) (P => (Q => R)) => S);

symbol NRM6 [H : El (list prd)] [P Q R S : El prd] [x : El idt] :
  ▷ (H ⟝ ♢ (x ⋅) (R => P) => (♢ (x ⋅) (R => Q) => S)) →
  ▷ (H ⟝ ♢ (x ⋅) (R => P and Q) => S);

symbol NRM7 [H : El (list prd)] [P Q S : El prd] [x : El idt] :
  ▷ (H ⟝ (♢ (x ⋅) P) => ((♢ (x ⋅) Q) => S)) →
  ▷ (H ⟝ (♢ (x ⋅) (P and Q) => S));

symbol NRM8 [H : El (list prd)] [Q S : El prd] [xs ys : El vrb] :
  ▷ (H ⟝ (♢ (concat xs ys) Q) => S) →
  ▷ (H ⟝ (♢ (xs) (! (ys) Q)) => S);

symbol NRM9 [H : El (list prd)] [P Q S : El prd] [x y : El idt] :
  ▷ (H ⟝ ♢ (x ⋅) (♢ (y ⋅) (P => Q) => S)) →
  ▷ (H ⟝ ♢ (x ⋅) (P => ! (y ⋅) Q) => S);

symbol NRM10 [H : El (list prd)] [P Q R : El prd] [x : El idt] :
  ▷ (H ⟝ ♡ (x ⋅) (not (P and Q)) => R) →
  ▷ (H ⟝ ♢ (x ⋅) (P and Q => FAUX) => R);

symbol NRM11 [H : El (list prd)] [P R : El prd] [x : El idt] :
  ▷ (H ⟝ ♡ (x ⋅) (not (VRAI and P)) => R) →
  ▷ (H ⟝ ♢ (x ⋅) (P => FAUX) => R);

symbol NRM12 [H : El (list prd)] [P Q R : El prd] [x : El idt] :
  ▷ (H ⟝ ♡ (x ⋅) (not (P and Q) => R)) →
  ▷ (H ⟝ ♢ (x ⋅) ((P => not Q) => R));

symbol NRM13 [H : El (list prd)] [P Q R : El prd] [xs : El vrb] :
  ▷ (H ⟝ ♡ (xs) (not (P and not Q)) => R) →
  ▷ (H ⟝ ♢ (xs) (P => Q) => R);

symbol NRM14 [H : El (list prd)] [P R : El prd] [xs : El vrb] :
  ▷ (H ⟝ ♡ xs not (VRAI and P) => R) →
  ▷ (H ⟝ (♢ xs (not P)) => R);

symbol NRM15 [H : El (list prd)] [P R : El prd] [x : El idt] :
  ▷ (H ⟝ ♡ (x ⋅) not (VRAI and not P) => R) →
  ▷ (H ⟝ (♢ (x ⋅) P) => R);

symbol NRM16 [H : El (list prd)] [P : El prd] [Q : El prd] [x : El idt] :
  ✓ ((! (x ⋅) P) ⋿ H) (H ⟝ Q) →
  ▷ (H ⟝ (♡ (x ⋅) P) => Q);

symbol NRM17 [H : El (list prd)] [P Q R : El prd] [E : El exp] [x y : El idt] :
  ✓ (((! (x ⋅) not (VRAI and P)) ⋿ H) && (subst x E P == R))
    (H ⟝ (♡ (y ⋅) (not (VRAI and (not P))) => Q));

// ----------------------------------------------
// 5.13. Rules for equality
// ----------------------------------------------
symbol EVR1 [H : El (list prd)] [P : El prd] [E : El exp] :
  ▷ (H ⟝ not (E = E) => P);

symbol EVR2 [H : El (list prd)] [E : El exp] :
  ▷ (H ⟝ FAUX) →
  ▷ (H ⟝ not (E = E));

symbol EVR2_1 [H : El (list prd)] [E : El exp] :
  Res (H ⟝ FAUX) →
  Res (H ⟝ not (E = E))
≔
 (λ ρ, result (obtain ρ));

symbol EVR3 [H : El (list prd)] [P : El prd] [E : El exp] :
  ▷ (H ⟝ P) →
  ▷ (H ⟝ not (E = E));

symbol EVR4 [H : El (list prd)] [E : El exp] :
  ▷ (H ⟝ (E = E));

symbol EAXM1 [H : El (list prd)] [E F : El exp] [P : El prd] :
  ✓ (elem (not (F = E)) H) (H ⟝ (E = F) => P);

symbol EAXM2 [H : El (list prd)] [E F : El exp] [P : El prd] :
  ✓ (elem (F = E) H) (H ⟝ not (E = F) => P);

symbol EAXM3_1 [H : El (list prd)] [E F : El exp] [P : El prd] :
  ✓ (elem (F = E) H) (H ⟝ (E = F));

symbol EAXM3_2 [H : El (list prd)] [E F : El exp] [P : El prd] :
  ✓ (elem (not (F = E)) H) (H ⟝ not (E = F));

symbol EIMP5_1 [H : El (list prd)] [E F : El exp] [P : El prd] :
  ✓ ((not (F = E)) ⋿ H) (H ⟝ P) →
  ▷ (H ⟝ not (E = F) => P);

symbol EIMP5_2 [H : El (list prd)] [E F : El exp] [P : El prd] :
  ✓ ((F = E) ⋿ H) (H ⟝ P) →
  ▷ (H ⟝ (E = F) => P);

symbol EQC1 [H : El (list prd)] [a b c d : El exp] [P : El prd] :
  ▷ (H ⟝ not (a = c) or not (b = d) => P) →
  ▷ (H ⟝ not (opair a b = opair c d) => P);

symbol EQC2 [H : El (list prd)] [a b c d : El exp] [P : El prd] :
  ▷ (H ⟝ (a = c) and (b = d) => P) →
  ▷ (H ⟝ (opair a b = opair c d) => P);

symbol EQS1 [H : El (list prd)] [E F : El exp] [P : El prd] :
  ▷ (H ⟝ (E = F) => P) →
  ▷ (H ⟝ (eql_set E F) => P);

symbol EQS2 [H : El (list prd)] [E F : El exp] [P : El prd] :
  ▷ (H ⟝ FAUX => P) →
  ▷ (H ⟝ not (eql_set E F) => P);

// ----------------------------------------------
// 5.14. Rules for arithmetic
// ----------------------------------------------
symbol AR1 [H : El (list prd)] [E : El exp] [R : El prd] :
  ▷ (H ⟝ R) →
  ▷ (H ⟝ (E ≤ E) => R);

symbol AR2 [a b : El exp] [H : El (list prd)] [R : El prd] :
  ✓ (ev (a > b)) (H ⟝ a ≤ b => R);

symbol AR3 [a : El exp] [H : El (list prd)] [R : El prd] :
  ▷ (H ⟝ ((𝟏 - a) ≤ 𝟎) => R) →
  ▷ (H ⟝ not (a ≤ 𝟎) => R);

symbol AR4 [E F : El exp] [H : El (list prd)] [R : El prd] :
  ✓ (((F ≤ 𝟎) ⋿ H) && (ev ((E + F) > 𝟎))) (H ⟝ E ≤ 𝟎 => R);

symbol AR5 [a : El exp] [H : El (list prd)] [R : El prd] :
  ✓ (elem (a ≪ 𝟎) H) (H ⟝ (a = 𝟎 => (⨪ a ≤ 𝟎 => R))) →
  ▷ (H ⟝ ⨪ a ≤ 𝟎 => R);

symbol AR6 [a : El exp] [H : El (list prd)] [R : El prd] :
  ✓ (elem (⨪ a ≪ 𝟎) H) (H ⟝ (a = 𝟎 => (a ≤ 𝟎 => R))) →
  ▷ (H ⟝ a ≤ 𝟎 => R);

// ----------------------------------------------
// 5.15 Booleans
// ----------------------------------------------
symbol FALSE : El exp;
symbol TRUE : El exp;

symbol BOOL1_1 [H : El (list prd)] [P : El prd] [v : El exp] :
  ▷ (cons (not (v = FALSE)) (cons (v = TRUE) H) ⟝ P) →
  ▷ (H ⟝ (v = TRUE) => P);

symbol BOOL1_2 [H : El (list prd)] [P : El prd] [v : El exp] :
  ▷ (cons (v = FALSE) (cons (not (v = TRUE)) H) ⟝ P) →
  ▷ (H ⟝ (v = FALSE) => P);

symbol BOOL2_1 [H : El (list prd)] [P : El prd] [v : El exp] :
  ▷ (H ⟝ (v = TRUE) => P) →
  ▷ (H ⟝ (TRUE = v) => P);

symbol BOOL2_2 [H : El (list prd)] [P : El prd] [v : El exp] :
  ▷ (H ⟝ (v = FALSE) => P) →
  ▷ (H ⟝ (FALSE = v) => P);

symbol BOOL3_1 [H : El (list prd)] [P : El prd] [v : El exp] :
  ▷ (H ⟝ (v = FALSE) => P) →
  ▷ (H ⟝ not (v = TRUE) => P);

symbol BOOL3_2 [H : El (list prd)] [P : El prd] [v : El exp] :
  ▷ (H ⟝ (v = TRUE) => P) →
  ▷ (H ⟝ not (v = FALSE) => P);

symbol BOOL4_1 [H : El (list prd)] [P : El prd] [v : El exp] :
  ▷ (H ⟝ (v = FALSE) => P) →
  ▷ (H ⟝ not (TRUE = v) => P);

symbol BOOL4_2 [H : El (list prd)] [P : El prd] [v : El exp] :
  ▷ (H ⟝ (v = TRUE) => P) →
  ▷ (H ⟝ not (FALSE = v) => P);

symbol BOOL5_1 [H : El (list prd)] [P : El prd] [v : El exp] :
  ▷ (H ⟝ (TRUE = FALSE) => P);

symbol BOOL5_2 [H : El (list prd)] [P : El prd] [v : El exp] :
  ▷ (H ⟝ (FALSE = TRUE) => P);
