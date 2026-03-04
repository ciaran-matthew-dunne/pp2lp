require open Stdlib.Prop Stdlib.Bool Stdlib.Classic Stdlib.Eq Stdlib.String Stdlib.FOL Stdlib.HOL;
require pp2lp.B as B;

sequential symbol str_eq : String → String → 𝔹;
rule str_eq $s $s ↪ true
with str_eq _ _   ↪ false;

// Axiom: str_eq is sound. Required because String is an opaque builtin
// type with no induction principle. Everything else is proved from this.
symbol str_eq_sound (s1 s2 : String) : π (istrue (str_eq s1 s2)) → π (s1 = s2);

// Set code for valuations.
symbol val ≔ string ⤳ ι;
symbol Val ≔ τ val;
symbol vnil : Val;
symbol vcons : Val → String → τ ι → Val;

rule (vcons $μ $s1 $x) $s2
  ↪ if (str_eq $s1 $s2) $x ($μ $s2);

symbol sat : Val → B.Prd → Prop;
symbol den : Val → B.Exp → τ ι;

rule sat $μ ((B.¬) $P)    ↪ ¬ (sat $μ $P)
with sat $μ ((B.∧) $P $Q) ↪ (sat $μ $P) ∧ (sat $μ $Q)
with sat $μ ((B.∨) $P $Q) ↪ (sat $μ $P) ∨ (sat $μ $Q)
with sat $μ ((B.⇒) $P $Q) ↪ (sat $μ $P) ⇒ (sat $μ $Q)
with sat $μ ((B.⇔) $P $Q) ↪ (sat $μ $P) ⇔ (sat $μ $Q)
with sat $μ ((B.=) $X $Y) ↪ (den $μ $X) = (den $μ $Y)
with sat $μ ((B.∀) (B.id $x) $P)
  ↪ `∀ y, (sat (vcons $μ $x y) $P)
with sat $μ ((B.∃) (B.id $x) $P)
  ↪ `∃ y, (sat (vcons $μ $x y) $P);


rule den $μ (B.#var (B.id $x)) ↪ $μ $x;
//with den $μ ((B.↦) $X $Y) ↪
//with den $μ ((B.×) $X $Y) ↪
//with den $μ ((B.𝒫) $X) ↪
//with den $μ (B.big) ↪
//with den $μ ((B.choice) $X) ↪
//with den $μ ((B.comp) $x $Y) ↪

symbol sem : Val → B.Hyp → Prop;
rule sem $μ (B.⦳)         ↪ ⊤
with sem $μ ((B.∷) $H $P) ↪ (sem $μ $H) ∧ (sat $μ $P);

rule B.▷ ((B.⟝) $H $P) ↪ π (sem vnil $H) → π (sat vnil $P);
