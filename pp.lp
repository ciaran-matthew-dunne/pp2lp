require open Logic.U.Set Logic.U.Prop;

symbol oops : TYPE;
symbol exp : TYPE;
symbol frm : TYPE;
symbol vrb : TYPE;
builtin "String" ≔ vrb; // : TYPE, for the type of strings

builtin "Prop" ≔ Prop; // : TYPE, for the type of propositions
builtin "P"    ≔ Prf; // : Prop → TYPE, interpretation of propositions as types

inductive prd : TYPE ≔
  | ∧ : prd → prd → prd
  | ∨ : prd → prd → prd
  | ⟹ : prd → prd → prd
  | ⟺ : prd → prd → prd
  | ¬ : prd → prd
  | ∀ : (exp → prd) → prd
  | ∃ : (exp → prd) → prd
  | = : exp → exp → prd
  | PROP : frm → prd;

inductive hyps : TYPE ≔
  | nil : hyps
  | cons : hyps → prd → hyps;

sequential symbol ⋿ : prd → hyps → Prop;
notation ⋿ infix 1;

rule ($P ⋿ nil) ↪ ⊥
with ($P ⋿ cons $H $P) ↪ ⊤
with ($P ⋿ cons $H $Q) ↪ ($P ⋿ $H);


symbol true : prd;
symbol false : prd;
symbol sequent : TYPE;


injective symbol ⊩ : hyps → prd → sequent;
injective symbol ✓ : sequent → TYPE;
injective symbol ⚀ : Prop → sequent → TYPE;

rule (⚀ ⊤ $Σ) ↪ (✓ $Σ);

notation ⊩ infix 0;
notation ∀ quantifier;
notation ∃ quantifier;
notation = infix left 5;
notation ¬ prefix 4;
notation ∧  infix left 3;
notation ∨  infix left 3;
notation ⟹ infix left 1;
notation ⟺ infix left 2;

// #################
// 5.1. Conjunction
// #################

symbol AND1 [H P Q R] :
  ✓ (H ⊩ ¬ Q ⟹ R) →
  ✓ (H ⊩ ¬ P ⟹ R) →
//--------------------------
  ✓ (H ⊩ ¬ (P ∧ Q) ⟹ R);

symbol AND2 [H P Q] :
  ✓ (H ⊩ P ⟹ ¬ Q) →
//-------------------
  ✓ (H ⊩ ¬ (P ∧ Q));

symbol AND3 [H P Q R] :
  ✓ (H ⊩ P ⟹ (Q ⟹ R)) →
//-------------------
  ✓ (H ⊩ (P ∧ Q) ⟹ R);

symbol AND4 [H P Q] :
  ✓ (H ⊩ P) →
  ✓ (H ⊩ Q) →
//-------------------
  ✓ (H ⊩ (P ∧ Q));

//symbol AND5 [H : hyps] [P R A B : prd]

// #################
// 5.2. Disjunction
// #################

symbol OR1 [H P Q R] :
  ✓ (H ⊩ ¬ P ⟹ (¬ Q ⟹ R)) →
//-------------------
  ✓ (H ⊩ ¬ (P ∨ Q) ⟹ R);

symbol OR2 [H : hyps] [P Q R : prd] :
  ✓ (H ⊩ ¬ Q) →
  ✓ (H ⊩ ¬ P) →
//-------------------
  ✓ (H ⊩ ¬ (P ∨ Q));

symbol OR3 [H : hyps] [P Q R : prd] :
  ✓ (H ⊩ Q ⟹ R) →
  ✓ (H ⊩ P ⟹ R) →
//-------------------
  ✓ (H ⊩ (P ∨ Q) ⟹ R);

symbol OR4 [H : hyps] [P Q : prd] :
  ✓ (H ⊩ ¬ P ⟹ Q) →
//-------------------
  ✓ (H ⊩ (P ∨ Q));

// #################
// 5.3. Implication
// #################

symbol IMP4 [H P Q] :
  ✓ (cons H P ⊩ Q) →
  ✓ (H ⊩ P ⟹ Q);

symbol NOT1 [H P R] :
  ✓ (H ⊩ P ⟹ R) →
  ✓ (H ⊩ ¬ ¬ P ⟹ R);

// #################
// 5.4. Equivalence
// #################

// #################
// 5.5. Negation
// #################

// #################
// 5.6. Axioms
// #################

symbol AXM1 [H P Q] :
  Prf (¬ P ⋿ H) → ✓ (H ⊩ P ⟹ Q);

symbol AXM2 [H P Q] :
  Prf (P ⋿ H) → ✓ (H ⊩ ¬ P ⟹ Q);

symbol AXM3 [H P] :
  Prf (P ⋿ H) → ✓ (H ⊩ P);

symbol AXM4 [H P R] :
  Prf (R ⋿ H) → ✓ (H ⊩ P ⟹ R);

// #############################
// 5.7. Universal quantification
// #############################

// ###############################
// 5.8. Existential quantification
// ###############################

// #############################
// 5.9. True and False
// #############################

// #############################
// 5.10. STOP rules
// #############################

// #############################
// 5.11. INS rules
// #############################

// #############################
// 5.12. Normalization
// #############################

// #############################
// 5.13. Rules for equality
// #############################

// #############################
// 5.14. Rules for arithmetic
// #############################

// #############################
// 5.15. Rules for booleans
// #############################

symbol thm : prd → TYPE ≔
  (λ P, ✓ (nil ⊩ P));

symbol COND [Ψ : Prop] [Σ : sequent]:
  Prf Ψ → ⚀ Ψ Σ → ✓ Σ;

symbol TOP : Π r, Prf r → Prf r;

symbol trace_01 (p q : prd) : thm ((¬ (p ∧ q)) ⟹ (¬ p ∨ ¬ q)) ≔
// manual reconstruction of `01.trace`
//  [AXM1] &
//  [NOT1] &
//  [OR4] &
//  [IMP4] &
//  [AXM4] &
//  [OR4] &
//  [IMP4] &
//  [AND1] &
//   (not(p and q) => not(p) or not(q))
begin
    assume p q;
    simplify;
    apply AND1
      {apply IMP4;
       apply OR4;
       apply AXM4;
       simplify;
       refine TOP;
       }
      {apply IMP4;
       apply OR4;
       apply NOT1;
       apply AXM1;
       simplify;
       refine TOP;}
  end;
