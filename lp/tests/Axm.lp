// Tests for rules/Axm.lp (axiom / hypothesis-lookup rules).
require open pp2lp.Prelude;

symbol t_AXM1 (P Q : Prop) (h : π (¬ P)) : π (P ⇒ Q) ≔ AXM1 h;
symbol t_AXM2 (P Q : Prop) (h : π P) : π (¬ P ⇒ Q) ≔ AXM2 h;
symbol t_AXM3 (P : Prop) (h : π P) : π P ≔ AXM3 h;
symbol t_AXM4 (P R : Prop) (h : π R) : π (P ⇒ R) ≔ AXM4 h;
symbol t_AXM5 (P Q R : Prop) (h : π (¬ Q)) : π (P ⇒ (Q ⇒ R)) ≔ AXM5 h;
symbol t_AXM6 (P Q R : Prop) (h : π Q) : π (P ⇒ (¬ Q ⇒ R)) ≔ AXM6 h;
symbol t_AXM7 (P : Prop) : π (P ⇒ P) ≔ @AXM7 P;
symbol t_AXM8 (C r : Prop) (f : π C → π r) : π (C ⇒ r) ≔ AXM8 f;
symbol t_AXM9 (n : ℕ) (P : Tuple n → Prop) (v : Tuple n) (Q : Prop)
  (h : π (`!! u, ¬ ⋀ (∎ ∷ ⊤ ∷ P u))) : π (P v ⇒ Q) ≔ AXM9 v h;

// _1 (Result-form) variants
symbol t_AXM1_1 (P Q : Prop) (h : π (¬ P)) : Res (P ⇒ Q) ≔ AXM1_1 h;
symbol t_AXM2_1 (P Q : Prop) (h : π P) : Res (¬ P ⇒ Q) ≔ AXM2_1 h;
symbol t_AXM3_1 (P : Prop) (h : π P) : Res P ≔ AXM3_1 h;
symbol t_AXM4_1 (P R : Prop) (h : π R) : Res (P ⇒ R) ≔ AXM4_1 h;
symbol t_AXM5_1 (P Q R : Prop) (h : π (¬ Q)) : Res (P ⇒ (Q ⇒ R)) ≔ AXM5_1 h;
symbol t_AXM6_1 (P Q R : Prop) (h : π Q) : Res (P ⇒ (¬ Q ⇒ R)) ≔ AXM6_1 h;
symbol t_AXM7_1 (P : Prop) : Res (P ⇒ P) ≔ @AXM7_1 P;
symbol t_AXM8_1 (C r : Prop) (f : π C → π r) : Res (C ⇒ r) ≔ AXM8_1 f;
symbol t_AXM9_1 (n : ℕ) (P : Tuple n → Prop) (v : Tuple n) (Q : Prop)
  (h : π (`!! u, ¬ ⋀ (∎ ∷ ⊤ ∷ P u))) : Res (P v ⇒ Q) ≔ AXM9_1 v h;
