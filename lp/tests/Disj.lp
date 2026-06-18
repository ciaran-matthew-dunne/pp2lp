// Tests for rules/Disj.lp.
require open pp2lp.Prelude;

symbol t_OR1 (P Q R : Prop) (h : π (¬ P ⇒ (¬ Q ⇒ R))) : π (¬ (P ∨ Q) ⇒ R) ≔ OR1 h;
symbol t_OR2 (P Q : Prop) (h1 : π (¬ Q)) (h2 : π (¬ P)) : π (¬ (P ∨ Q)) ≔ OR2 h1 h2;
symbol t_OR3 (P Q R : Prop) (h1 : π (Q ⇒ R)) (h2 : π (P ⇒ R)) : π ((P ∨ Q) ⇒ R) ≔ OR3 h1 h2;
symbol t_OR4 (P Q : Prop) (h : π (¬ P ⇒ Q)) : π (P ∨ Q) ≔ OR4 h;

// _1 (Result-form) variants
symbol t_OR1_1 (P Q R : Prop) (r : Res (¬ P ⇒ ¬ Q ⇒ R)) : Res (¬ (P ∨ Q) ⇒ R) ≔ OR1_1 r;
symbol t_OR2_1 (P Q : Prop) (r1 : Res (¬ Q)) (r2 : Res (¬ P)) : Res (¬ (P ∨ Q)) ≔ OR2_1 r1 r2;
symbol t_OR3_1 (P Q R : Prop) (r1 : Res (Q ⇒ R)) (r2 : Res (P ⇒ R)) : Res ((P ∨ Q) ⇒ R) ≔ OR3_1 r1 r2;
symbol t_OR4_1 (P Q : Prop) (r : Res (¬ P ⇒ Q)) : Res (P ∨ Q) ≔ OR4_1 r;
