// Tests for rules/Neg.lp — each rule applied to a goal of its spec shape.
// The symbol's declared type pins the intended statement; the body applies
// the named rule, so a drift in the rule's type breaks the test.
require open pp2lp.Prelude;

symbol t_NOT1 (P R : Prop) (h : π (P ⇒ R)) : π (¬ ¬ P ⇒ R) ≔ NOT1 h;
symbol t_NOT2 (P : Prop) (h : π P) : π (¬ ¬ P) ≔ NOT2 h;

// _1 (Result-form) variants
symbol t_NOT1_1 (P R : Prop) (r : Res (P ⇒ R)) : Res (¬ ¬ P ⇒ R) ≔ NOT1_1 r;
symbol t_NOT2_1 (P : Prop) (r : Res P) : Res (¬ ¬ P) ≔ NOT2_1 r;
