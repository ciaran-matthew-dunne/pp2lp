// Tests for rules/TrueFalse.lp (TRUE / FALSE / STOP / INS).
require open pp2lp.Prelude;

symbol t_VR1 (R : Prop) : π (¬ ⊤ ⇒ R) ≔ VR1;
symbol t_VR2 (h : π ⊥) : π (¬ ⊤) ≔ VR2 h;
symbol t_VR3 (R : Prop) (h : π R) : π (⊤ ⇒ R) ≔ VR3 h;
symbol t_VR4 : π ⊤ ≔ VR4;
symbol t_FX1 (R : Prop) (h : π R) : π (¬ ⊥ ⇒ R) ≔ FX1 h;
symbol t_FX2 : π (¬ ⊥) ≔ FX2;
symbol t_FX3 (R : Prop) : π (⊥ ⇒ R) ≔ FX3;
symbol t_STOP (P : Prop) (h : π (¬ P ⇒ ⊥)) : π P ≔ STOP h;

// _1 (Result-form) variants
symbol t_STOP_1 (P : Prop) : Res P ≔ @STOP_1 P;
symbol t_VR1_1 (R : Prop) : Res (¬ ⊤ ⇒ R) ≔ @VR1_1 R;
symbol t_VR2_1 (r : Res ⊥) : Res (¬ ⊤) ≔ VR2_1 r;
symbol t_VR3_1 (P : Prop) (r : Res P) : Res (⊤ ⇒ P) ≔ VR3_1 r;
symbol t_VR4_1 : Res ⊤ ≔ VR4_1;
symbol t_FX1_1 (R : Prop) (r : Res R) : Res (¬ ⊥ ⇒ R) ≔ FX1_1 r;
symbol t_FX2_1 : Res (¬ ⊥) ≔ FX2_1;
symbol t_FX3_1 (R : Prop) : Res (⊥ ⇒ R) ≔ @FX3_1 R;
symbol t_INS_1 (P : Prop) (h : π ⊥) : Res P ≔ INS_1 h;
