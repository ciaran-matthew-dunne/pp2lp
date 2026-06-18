// Tests for rules/Impl.lp.
require open pp2lp.Prelude;

symbol t_IMP1 (P Q R : Prop) (h : π (P ⇒ (¬ Q ⇒ R))) : π (¬ (P ⇒ Q) ⇒ R) ≔ IMP1 h;
symbol t_IMP2 (P Q : Prop) (h1 : π (¬ Q)) (h2 : π P) : π (¬ (P ⇒ Q)) ≔ IMP2 h1 h2;
symbol t_IMP3 (P Q R : Prop) (h1 : π (Q ⇒ R)) (h2 : π (¬ P ⇒ R)) : π ((P ⇒ Q) ⇒ R) ≔ IMP3 h1 h2;
symbol t_IMP4 (P Q : Prop) (h : π P → π Q) : π (P ⇒ Q) ≔ IMP4 h;
symbol t_IMP5 (P Q : Prop) (h : π Q) : π (P ⇒ Q) ≔ IMP5 h;

// _1 (Result-form) variants
symbol t_IMP1_1 (P Q R : Prop) (r : Res (P ⇒ ¬ Q ⇒ R)) : Res (¬ (P ⇒ Q) ⇒ R) ≔ IMP1_1 r;
symbol t_IMP2_1 (P Q : Prop) (r1 : Res (¬ Q)) (r2 : Res P) : Res (¬ (P ⇒ Q)) ≔ IMP2_1 r1 r2;
symbol t_IMP3_1 (P Q R : Prop) (r1 : Res (Q ⇒ R)) (r2 : Res (¬ P ⇒ R)) : Res ((P ⇒ Q) ⇒ R) ≔ IMP3_1 r1 r2;
symbol t_IMP4_1 (P Q : Prop) (r : Res Q) : Res (P ⇒ Q) ≔ @IMP4_1 P Q r;
symbol t_IMP4_1U (P Q R : Prop) (f : π P → π (Q = R)) : Res (P ⇒ Q) ≔ IMP4_1U f;
symbol t_IMP5_1 (P Q : Prop) (hp : π P) (r : Res Q) : Res (P ⇒ Q) ≔ IMP5_1 hp r;
