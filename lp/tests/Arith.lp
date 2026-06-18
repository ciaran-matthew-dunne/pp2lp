// Tests for rules/Arith.lp (linear arithmetic over leq).
require open pp2lp.Prelude;

symbol t_AR1 (E : τ ι) (R : Prop) (h : π R) : π ((leq E E) ⇒ R) ≔ AR1 h;
symbol t_AR2 (a b : Stdlib.Z.ℤ) (R : Prop) (h : π (Stdlib.Z.> a b))
  : π ((leq (from_int a) (from_int b)) ⇒ R) ≔ AR2 h;  // a, b, R implicit (from_int injective)
symbol t_AR3 (a r : τ ι) (R : Prop) (eq : π (minus 𝟏 a = r)) (h : π ((leq r 𝟎) ⇒ R))
  : π (¬ (leq a 𝟎) ⇒ R) ≔ AR3 a r eq h;
symbol t_AR4 (E : τ ι) (R : Prop) (F : τ ι) (hF : π (leq F 𝟎)) (hEF : π (gt (plus E F) 𝟎))
  : π ((leq E 𝟎) ⇒ R) ≔ AR4 hF hEF;
symbol t_AR5 (a : τ ι) (R : Prop) (hai : π (a ϵ INT)) (h1 : π (a ≪ 𝟎))
  (h2 : π ((leq (neg a) 𝟎) ⇒ ((a = 𝟎) ⇒ R)))
  : π ((leq (neg a) 𝟎) ⇒ R) ≔ AR5 hai h1 h2;
symbol t_AR6 (a : τ ι) (R : Prop) (hai : π (a ϵ INT)) (h1 : π ((leq (neg a) 𝟎)))
  (h2 : π ((leq a 𝟎) ⇒ ((a = 𝟎) ⇒ R)))
  : π ((leq a 𝟎) ⇒ R) ≔ AR6 hai h1 h2;
symbol t_AR7 (a b c : τ ι) (R : Prop)
  (hai : π (a ϵ INT)) (hbi : π (b ϵ INT)) (hci : π (c ϵ INT))
  (h1 : π ((plus c b) ≪ 𝟎)) (h2 : π ((plus a c) = 𝟎))
  (h3 : π ((b = a) ⇒ ((leq (minus a b) 𝟎) ⇒ R)))
  : π ((leq (minus a b) 𝟎) ⇒ R) ≔ AR7 c hai hbi hci h1 h2 h3;
symbol t_AR8 (a b c : τ ι) (R : Prop)
  (hai : π (a ϵ INT)) (hbi : π (b ϵ INT)) (hci : π (c ϵ INT))
  (h1 : π ((minus a b) ≪ 𝟎)) (h2 : π ((plus a c) = 𝟎))
  (h3 : π ((b = a) ⇒ ((leq (plus c b) 𝟎) ⇒ R)))
  : π ((leq (plus c b) 𝟎) ⇒ R) ≔ AR8 a hai hbi hci h1 h2 h3;
symbol t_AR9 (E F : τ ι) (R : Prop) (h1 : π (E = F)) (h2 : π ((leq F 𝟎) ⇒ R))
  : π ((leq E 𝟎) ⇒ R) ≔ AR9 F h1 h2;
symbol t_AR10 (P Q R : Prop) (h1 : π (P = Q)) (h2 : π (Q ⇒ R)) : π (P ⇒ R) ≔ AR10 h1 h2;
symbol t_AR11 (E : τ ι) (P : Prop) : π (¬ (leq E E) ⇒ P) ≔ @AR11 E P;
symbol t_AR12 (a b : τ ι) (P : Prop) (h : π (leq a b) → π P) : π ((leq a b) ⇒ P) ≔ AR12 h;
symbol t_AR13 (a b : τ ι) (h1 : π ((minus 𝟏 a) = b)) (h2 : π (leq b 𝟎))
  : π (¬ (leq a 𝟎)) ≔ AR13 h1 h2;

// _1 (Result-form) variants
symbol t_AR1_1 (E : τ ι) (R : Prop) (r : Res R) : Res ((leq E E) ⇒ R) ≔ @AR1_1 E R r;
symbol t_AR3_1 (a r : τ ι) (R : Prop) (eq : π (minus 𝟏 a = r)) (cont : Res ((leq r 𝟎) ⇒ R))
  : Res (¬ (leq a 𝟎) ⇒ R) ≔ AR3_1 a r eq cont;
symbol t_AR4_1 (E : τ ι) (R : Prop) (F : τ ι) (hf : π (leq F 𝟎)) (hef : π (gt (plus E F) 𝟎))
  : Res ((leq E 𝟎) ⇒ R) ≔ AR4_1 F hf hef;
symbol t_AR5_1 (a : τ ι) (R : Prop) (h0 : π (a = 𝟎))
  (r : Res ((leq (neg a) 𝟎) ⇒ ((a = 𝟎) ⇒ R))) : Res ((leq (neg a) 𝟎) ⇒ R) ≔ AR5_1 h0 r;
symbol t_AR6_1 (a : τ ι) (R : Prop) (h0 : π (a = 𝟎))
  (r : Res ((leq a 𝟎) ⇒ ((a = 𝟎) ⇒ R))) : Res ((leq a 𝟎) ⇒ R) ≔ AR6_1 h0 r;
symbol t_AR7_1 (a b c : τ ι) (R : Prop) (hab : π (a = b))
  (r : Res ((a = b) ⇒ ((leq (minus a b) 𝟎) ⇒ R))) : Res ((leq (minus a b) 𝟎) ⇒ R) ≔ AR7_1 c hab r;
symbol t_AR8_1 (a b c : τ ι) (R : Prop) (hab : π (a = b))
  (r : Res ((a = b) ⇒ ((leq (plus c b) 𝟎) ⇒ R))) : Res ((leq (plus c b) 𝟎) ⇒ R) ≔ AR8_1 a hab r;
symbol t_AR9_1 (E F : τ ι) (R : Prop) (he : π (E = F)) (r : Res ((leq F 𝟎) ⇒ R))
  : Res ((leq E 𝟎) ⇒ R) ≔ AR9_1 F he r;
symbol t_AR10_1 (P Q R : Prop) (heq : π (P = Q)) (r : Res (Q ⇒ R)) : Res (P ⇒ R) ≔ AR10_1 heq r;
symbol t_AR11_1 (E : τ ι) (P : Prop) : Res (¬ (leq E E) ⇒ P) ≔ @AR11_1 E P;
symbol t_AR12_1 (a b : τ ι) (P : Prop) (h : π (leq a b)) (r : Res P)
  : Res ((leq a b) ⇒ P) ≔ AR12_1 h r;
// b is a free implicit of AR13_1 (it appears nowhere in the type), so pass it.
symbol t_AR13_1 (a b : τ ι) (h : π (¬ (leq a 𝟎))) : Res (¬ (leq a 𝟎)) ≔ @AR13_1 a b h;
