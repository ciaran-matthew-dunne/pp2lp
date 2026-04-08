require open
  Stdlib.Prop Stdlib.Impred Stdlib.List Stdlib.HOL
  Stdlib.String;

sequential symbol explode : τ (o ⤳ list o);
rule explode ($p ∧ $q) ↪ $q ∷ (explode $p)
with explode $p ↪ $p ∷ □;

sequential symbol implode : τ (list o ⤳ o);
rule implode ($p ∷ □) ↪ $p
with implode ($p ∷ $ps) ↪ (implode $ps) ∧ $p;

symbol pid : String → Prop;
symbol foo ≔
  ((pid "p" ∧ (pid "a" ∧ pid "b")) ∧ pid "q");

type ∈;

symbol AND5 [R C : Prop] (A B : Prop)
  : π (A ∈ explode C) → π (C ⇒ R) ;
