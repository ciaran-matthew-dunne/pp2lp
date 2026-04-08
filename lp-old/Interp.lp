require open
  Stdlib.Prop Stdlib.Set
  Stdlib.List
  Stdlib.String Stdlib.FOL
  Stdlib.HOL
  Stdlib.Z;
require pp2lp.B as B;
require pp2lp.Eq as Eq;
require pp2lp.Proof as Proof;

// Set code for valuations.
symbol val ≔ string ⤳ ι;
symbol Val ≔ τ val;
symbol vnil : Val;
symbol vcons :
  Val → String → τ ι → Val;

symbol sat :
  Val → B.Prd → Prop;
symbol den :
  Val → B.Exp → τ ι;
type (B.¬);
rule sat $μ ((B.¬) $P)
  ↪ ¬ (sat $μ $P)
with sat $μ ((B.∧) $P $Q)
  ↪ (sat $μ $P) ∧ (sat $μ $Q)
with sat $μ ((B.∨) $P $Q)
  ↪ (sat $μ $P)
    ∨ (sat $μ $Q)
with sat $μ ((B.⇒) $P $Q)
  ↪ (sat $μ $P)
    ⇒ (sat $μ $Q)
with sat $μ ((B.⇔) $P $Q)
  ↪ (sat $μ $P)
    ⇔ (sat $μ $Q)
with sat $μ ((B.≃) $X $Y)
  ↪ (den $μ $X)
    = (den $μ $Y)
with sat $μ
    ((B.∀) (B.id $s) $P)
  ↪ `∀ z,
    (sat (vcons $μ $s z) $P)
with sat $μ
    ((B.∀)
      ((B.⨾) $x $y) $P)
  ↪ sat $μ
    (B.∀ $x (B.∀ $y $P))
with sat $μ
    ((B.∃) (B.id $s) $P)
  ↪ `∀ z,
    (sat (vcons $μ $s z) $P)
with sat $μ
    ((B.∃)
      ((B.⨾) $x $y) $P)
  ↪ sat $μ
    (B.∀ $x (B.∀ $y $P));

symbol opair :
  τ (ι ⤳ ι ⤳ ι);
symbol lift_ty : Set → Set;
rule lift_ty int ↪ ι
with lift_ty bool ↪ ι
with lift_ty ($a ⤳ $b)
  ↪ lift_ty $a ⤳ lift_ty $b;

symbol lift [a : Set] :
  τ a → τ (lift_ty a);
rule lift (+)
    (lift [int] $x)
    (lift [int] $y)
  ↪ lift ($x + $y)
with lift (-)
    (lift [int] $x)
    (lift [int] $y)
  ↪ lift ($x - $y)
with lift (—)
    (lift [int] $x)
  ↪ lift (— $x);

rule den $μ (B.eid $x)
  ↪ $μ $x
with den $μ ((B.↦) $E $F)
  ↪ opair (den $μ $E)
    (den $μ $F)
with den _ (B.𝟎) ↪ lift 0
with den _ (B.𝟏) ↪ lift 1
with den _ (B.BTRUE)
  ↪ lift true
with den _ (B.BFALSE)
  ↪ lift false
with den $μ ((B.+) $x $y)
  ↪ lift (+) (den $μ $x)
    (den $μ $y)
with den $μ ((B.-) $x $y)
  ↪ lift (-) (den $μ $x)
    (den $μ $y)
with den $μ ((B.⨪) $x)
  ↪ lift (—) (den $μ $x);

symbol sem :
  Val → Proof.Hyp → Prop;
rule sem $μ □ ↪ ⊤
with sem $μ ($P ∷ $H)
  ↪ (sat $μ $P) ∧ (sem $μ $H);

rule Proof.▷
    ((Proof.⟝) $H $P)
  ↪ π (sem vnil $H)
    → π (sat vnil $P);
