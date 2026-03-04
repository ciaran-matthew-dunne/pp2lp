// Minimal mutual inductive: Prd with Exp = just variables.
require open Stdlib.Bool Stdlib.Set Stdlib.Prop Stdlib.Eq Stdlib.FOL Stdlib.String;

// String equality (axiom, same as in the real development).
sequential symbol str_eq : String → String → 𝔹;
rule str_eq $s $s ↪ true
with str_eq _ _   ↪ false;

symbol str_eq_sound (s1 s2 : String) : π (istrue (str_eq s1 s2)) → π (s1 = s2);

// Minimal mutual inductive types.
inductive Prd : TYPE ≔
  | ¬   : Prd → Prd
  | ∧   : Prd → Prd → Prd
  | Eq  : Exp → Exp → Prd
with Exp : TYPE ≔
  | Var : String → Exp;

notation ¬ prefix 9;
notation ∧ infix left 8;

// Set codes.
symbol prd : Set; rule τ prd ↪ Prd;
symbol exp : Set; rule τ exp ↪ Exp;

// Print the induction principle type.
type ind_Prd;

// Syntactic equality.
sequential symbol prd_eq : Prd → Prd → 𝔹;
sequential symbol exp_eq : Exp → Exp → 𝔹;

rule prd_eq (¬ $p) (¬ $q)       ↪ prd_eq $p $q
with prd_eq ($p ∧ $q) ($r ∧ $s) ↪ (prd_eq $p $r) and (prd_eq $q $s)
with prd_eq (Eq $e $f) (Eq $g $h) ↪ (exp_eq $e $g) and (exp_eq $f $h)
with prd_eq _ _                  ↪ false;

rule exp_eq (Var $s) (Var $t) ↪ str_eq $s $t
with exp_eq _ _               ↪ false;

// ---- Motives ----

symbol p0 : Prd → Prop ≔
  λ P, `∀ Q : τ prd, istrue (prd_eq P Q) ⇒ (P = Q);

symbol p2 : Exp → Prop ≔
  λ E, `∀ F : τ exp, istrue (exp_eq E F) ⇒ (E = F);

// ---- shared case proofs ----

// case ¬ p
symbol c_neg (p : Prd) (ihp : π (p0 p)) : π (p0 (¬ p)) ≔
  λ Q, ind_Prd
    (λ Q, istrue (prd_eq (¬ p) Q) ⇒ ((¬ p) = Q))
    (λ e, ⊤)
    (λ q iq h, feq (λ (x : τ prd), ¬ x) (ihp q h))
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ s, ⊤ᵢ)
    Q;

// case p1 ∧ p2
symbol c_and (p1 : Prd) (ih1 : π (p0 p1)) (p2 : Prd) (ih2 : π (p0 p2))
  : π (p0 (p1 ∧ p2)) ≔
  λ Q, ind_Prd
    (λ Q, istrue (prd_eq (p1 ∧ p2) Q) ⇒ ((p1 ∧ p2) = Q))
    (λ e, ⊤)
    (λ q iq h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h,
      feq2 (λ (a : τ prd) (b : τ prd), a ∧ b)
        (ih1 q1 (@andₑ₁ (prd_eq p1 q1) (prd_eq p2 q2) h))
        (ih2 q2 (@andₑ₂ (prd_eq p1 q1) (prd_eq p2 q2) h)))
    (λ e1 ie1 e2 ie2 h, ⊥ₑ h)
    (λ s, ⊤ᵢ)
    Q;

// case Eq e1 e2
symbol c_eq (e1 : Exp) (ihe1 : π (p2 e1)) (e2 : Exp) (ihe2 : π (p2 e2))
  : π (p0 (Eq e1 e2)) ≔
  λ Q, ind_Prd
    (λ Q, istrue (prd_eq (Eq e1 e2) Q) ⇒ ((Eq e1 e2) = Q))
    (λ e, ⊤)
    (λ q iq h, ⊥ₑ h)
    (λ q1 iq1 q2 iq2 h, ⊥ₑ h)
    (λ f1 if1 f2 if2 h,
      feq2 (λ (a : τ exp) (b : τ exp), Eq a b)
        (ihe1 f1 (@andₑ₁ (exp_eq e1 f1) (exp_eq e2 f2) h))
        (ihe2 f2 (@andₑ₂ (exp_eq e1 f1) (exp_eq e2 f2) h)))
    (λ s, ⊤ᵢ)
    Q;

// case Var s
symbol c_var (s : String) : π (p2 (Var s)) ≔
  λ F, ind_Exp
    (λ e, ⊤)
    (λ F, istrue (exp_eq (Var s) F) ⇒ ((Var s) = F))
    (λ q iq, ⊤ᵢ) (λ q1 iq1 q2 iq2, ⊤ᵢ) (λ e1 ie1 e2 ie2, ⊤ᵢ)
    (λ t h, feq Var (str_eq_sound s t h))
    F;

// ---- prd_eq_sound ----

opaque symbol prd_eq_sound (P Q : Prd)
  : π (istrue (prd_eq P Q)) → π (P = Q) ≔
begin
  assume P; refine ind_Prd p0 p2 c_neg c_and c_eq c_var P
end;

// ---- exp_eq_sound ----

opaque symbol exp_eq_sound (E F : Exp)
  : π (istrue (exp_eq E F)) → π (E = F) ≔
begin
  assume E; refine ind_Exp p0 p2 c_neg c_and c_eq c_var E
end;
