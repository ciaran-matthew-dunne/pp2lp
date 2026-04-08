// Boolean (§A.15)
require open
  pp2lp.B pp2lp.Proof;

symbol BOOL11 [H v P]
  : ▷ ((¬ (v ≃ BFALSE)) ∷ (v ≃ BTRUE) ∷ H ⟝ P)
  → ▷ (H ⟝ (v ≃ BTRUE) ⇒ P);

symbol BOOL12 [H v P]
  : ▷ ((¬ (v ≃ BTRUE)) ∷ (v ≃ BFALSE) ∷ H ⟝ P)
  → ▷ (H ⟝ (v ≃ BFALSE) ⇒ P);

symbol BOOL21 [H v P]
  : ▷ (H ⟝ (v ≃ BTRUE) ⇒ P)
  → ▷ (H ⟝ (BTRUE ≃ v) ⇒ P);

symbol BOOL22 [H v P]
  : ▷ (H ⟝ (v ≃ BFALSE) ⇒ P)
  → ▷ (H ⟝ (BFALSE ≃ v) ⇒ P);

symbol BOOL31 [H v P]
  : ▷ (H ⟝ (v ≃ BFALSE) ⇒ P)
  → ▷ (H ⟝ ¬ (v ≃ BTRUE) ⇒ P);

symbol BOOL32 [H v P]
  : ▷ (H ⟝ (v ≃ BTRUE) ⇒ P)
  → ▷ (H ⟝ ¬ (v ≃ BFALSE) ⇒ P);

symbol BOOL41 [H v P]
  : ▷ (H ⟝ (v ≃ BFALSE) ⇒ P)
  → ▷ (H ⟝ ¬ (BTRUE ≃ v) ⇒ P);

symbol BOOL42 [H v P]
  : ▷ (H ⟝ (v ≃ BTRUE) ⇒ P)
  → ▷ (H ⟝ ¬ (BFALSE ≃ v) ⇒ P);

symbol BOOL51 [H P]
  : ▷ (H ⟝ (BTRUE ≃ BFALSE) ⇒ P);

symbol BOOL52 [H P]
  : ▷ (H ⟝ (BFALSE ≃ BTRUE) ⇒ P);

// ---- Primed variants ----

symbol BOOL11_1 [H v P]
  : Res ((¬ (v ≃ BFALSE)) ∷ (v ≃ BTRUE) ∷ H ⟝ P)
  → Res (H ⟝ (v ≃ BTRUE) ⇒ P);
rule obtain (BOOL11_1 $r) ↪ obtain $r;

symbol BOOL12_1 [H v P]
  : Res ((¬ (v ≃ BTRUE)) ∷ (v ≃ BFALSE) ∷ H ⟝ P)
  → Res (H ⟝ (v ≃ BFALSE) ⇒ P);
rule obtain (BOOL12_1 $r) ↪ obtain $r;

symbol BOOL21_1 [H v P]
  : Res (H ⟝ (v ≃ BTRUE) ⇒ P)
  → Res (H ⟝ (BTRUE ≃ v) ⇒ P);
rule obtain (BOOL21_1 $r) ↪ obtain $r;

symbol BOOL22_1 [H v P]
  : Res (H ⟝ (v ≃ BFALSE) ⇒ P)
  → Res (H ⟝ (BFALSE ≃ v) ⇒ P);
rule obtain (BOOL22_1 $r) ↪ obtain $r;

symbol BOOL31_1 [H v P]
  : Res (H ⟝ (v ≃ BFALSE) ⇒ P)
  → Res (H ⟝ ¬ (v ≃ BTRUE) ⇒ P);
rule obtain (BOOL31_1 $r) ↪ obtain $r;

symbol BOOL32_1 [H v P]
  : Res (H ⟝ (v ≃ BTRUE) ⇒ P)
  → Res (H ⟝ ¬ (v ≃ BFALSE) ⇒ P);
rule obtain (BOOL32_1 $r) ↪ obtain $r;

symbol BOOL41_1 [H v P]
  : Res (H ⟝ (v ≃ BFALSE) ⇒ P)
  → Res (H ⟝ ¬ (BTRUE ≃ v) ⇒ P);
rule obtain (BOOL41_1 $r) ↪ obtain $r;

symbol BOOL42_1 [H v P]
  : Res (H ⟝ (v ≃ BTRUE) ⇒ P)
  → Res (H ⟝ ¬ (BFALSE ≃ v) ⇒ P);
rule obtain (BOOL42_1 $r) ↪ obtain $r;

symbol BOOL51_1 [H P]
  : Res (H ⟝ (BTRUE ≃ BFALSE) ⇒ P);
rule obtain (BOOL51_1) ↪ TRUE;

symbol BOOL52_1 [H P]
  : Res (H ⟝ (BFALSE ≃ BTRUE) ⇒ P);
rule obtain (BOOL52_1) ↪ TRUE;
