// Tests for rules/Bool.lp (BOOL membership / equality rules).
require open pp2lp.Prelude;

symbol t_BOOL11 (V : τ ι) (P : Prop)
  (h : π (V = BTRUE) → π (¬ (V = BFALSE)) → π P) : π ((V = BTRUE) ⇒ P) ≔ BOOL11 h;
symbol t_BOOL12 (V : τ ι) (P : Prop)
  (h : π (V = BFALSE) → π (¬ (V = BTRUE)) → π P) : π ((V = BFALSE) ⇒ P) ≔ BOOL12 h;
symbol t_BOOL21 (V : τ ι) (P : Prop) (h : π ((V = BTRUE) ⇒ P)) : π ((BTRUE = V) ⇒ P) ≔ BOOL21 h;
symbol t_BOOL22 (V : τ ι) (P : Prop) (h : π ((V = BFALSE) ⇒ P)) : π ((BFALSE = V) ⇒ P) ≔ BOOL22 h;
symbol t_BOOL31 (V : τ ι) (P : Prop) (hb : π (V ϵ BOOL))
  (h : π ((V = BFALSE) ⇒ P)) : π (¬ (V = BTRUE) ⇒ P) ≔ BOOL31 hb h;
symbol t_BOOL32 (V : τ ι) (P : Prop) (hb : π (V ϵ BOOL))
  (h : π ((V = BTRUE) ⇒ P)) : π (¬ (V = BFALSE) ⇒ P) ≔ BOOL32 hb h;
symbol t_BOOL41 (V : τ ι) (P : Prop) (hb : π (V ϵ BOOL))
  (h : π ((V = BFALSE) ⇒ P)) : π (¬ (BTRUE = V) ⇒ P) ≔ BOOL41 hb h;
symbol t_BOOL42 (V : τ ι) (P : Prop) (hb : π (V ϵ BOOL))
  (h : π ((V = BTRUE) ⇒ P)) : π (¬ (BFALSE = V) ⇒ P) ≔ BOOL42 hb h;
symbol t_BOOL51 (P : Prop) : π ((BTRUE = BFALSE) ⇒ P) ≔ @BOOL51 P;
symbol t_BOOL52 (P : Prop) : π ((BFALSE = BTRUE) ⇒ P) ≔ @BOOL52 P;

// _1 (Result-form) variants
symbol t_BOOL11_1 (V : τ ι) (P : Prop) (h : π (V = BTRUE)) (r : Res P)
  : Res ((V = BTRUE) ⇒ P) ≔ BOOL11_1 h r;
symbol t_BOOL12_1 (V : τ ι) (P : Prop) (h : π (V = BFALSE)) (r : Res P)
  : Res ((V = BFALSE) ⇒ P) ≔ BOOL12_1 h r;
symbol t_BOOL21_1 (V : τ ι) (P : Prop) (r : Res ((V = BTRUE) ⇒ P))
  : Res ((BTRUE = V) ⇒ P) ≔ BOOL21_1 r;
symbol t_BOOL22_1 (V : τ ι) (P : Prop) (r : Res ((V = BFALSE) ⇒ P))
  : Res ((BFALSE = V) ⇒ P) ≔ BOOL22_1 r;
symbol t_BOOL31_1 (V : τ ι) (P : Prop) (hb : π (V ϵ BOOL)) (r : Res ((V = BFALSE) ⇒ P))
  : Res (¬ (V = BTRUE) ⇒ P) ≔ BOOL31_1 hb r;
symbol t_BOOL32_1 (V : τ ι) (P : Prop) (hb : π (V ϵ BOOL)) (r : Res ((V = BTRUE) ⇒ P))
  : Res (¬ (V = BFALSE) ⇒ P) ≔ BOOL32_1 hb r;
symbol t_BOOL41_1 (V : τ ι) (P : Prop) (hb : π (V ϵ BOOL)) (r : Res ((V = BFALSE) ⇒ P))
  : Res (¬ (BTRUE = V) ⇒ P) ≔ BOOL41_1 hb r;
symbol t_BOOL42_1 (V : τ ι) (P : Prop) (hb : π (V ϵ BOOL)) (r : Res ((V = BTRUE) ⇒ P))
  : Res (¬ (BFALSE = V) ⇒ P) ≔ BOOL42_1 hb r;
symbol t_BOOL51_1 (P : Prop) : Res ((BTRUE = BFALSE) ⇒ P) ≔ @BOOL51_1 P;
symbol t_BOOL52_1 (P : Prop) : Res ((BFALSE = BTRUE) ⇒ P) ≔ @BOOL52_1 P;
