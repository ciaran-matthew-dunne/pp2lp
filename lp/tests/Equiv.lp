// Tests for rules/Equiv.lp.
require open pp2lp.Prelude;

symbol t_EQV1 (P Q R : Prop) (h1 : π (P ⇒ (¬ Q ⇒ R))) (h2 : π (¬ P ⇒ (Q ⇒ R)))
  : π (¬ (P ⇔ Q) ⇒ R) ≔ EQV1 h1 h2;
symbol t_EQV2 (P Q : Prop) (h1 : π (P ⇒ ¬ Q)) (h2 : π (¬ Q ⇒ P)) : π (¬ (P ⇔ Q)) ≔ EQV2 h1 h2;
symbol t_EQV3 (P Q R : Prop) (h1 : π (P ⇒ (Q ⇒ R))) (h2 : π (¬ P ⇒ (¬ Q ⇒ R)))
  : π ((P ⇔ Q) ⇒ R) ≔ EQV3 h1 h2;
symbol t_EQV4 (P Q : Prop) (h1 : π (P ⇒ Q)) (h2 : π (Q ⇒ P)) : π (P ⇔ Q) ≔ EQV4 h1 h2;

// _1 (Result-form) variants
symbol t_EQV1_1 (P Q R : Prop) (r1 : Res (P ⇒ ¬ Q ⇒ R)) (r2 : Res (¬ P ⇒ Q ⇒ R))
  : Res (¬ (P ⇔ Q) ⇒ R) ≔ EQV1_1 r1 r2;
symbol t_EQV2_1 (P Q : Prop) (r1 : Res (P ⇒ ¬ Q)) (r2 : Res (¬ Q ⇒ P)) : Res (¬ (P ⇔ Q)) ≔ EQV2_1 r1 r2;
symbol t_EQV3_1 (P Q R : Prop) (r1 : Res (P ⇒ Q ⇒ R)) (r2 : Res (¬ P ⇒ ¬ Q ⇒ R))
  : Res ((P ⇔ Q) ⇒ R) ≔ EQV3_1 r1 r2;
symbol t_EQV4_1 (P Q : Prop) (r1 : Res (P ⇒ Q)) (r2 : Res (Q ⇒ P)) : Res (P ⇔ Q) ≔ EQV4_1 r1 r2;
