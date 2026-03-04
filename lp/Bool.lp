// Boolean rules (spec §A.15)
require open pp2lp.B pp2lp.Eq pp2lp.Interp;

// ---- base rules ----------------

// BOOL11: H, (v = TRUE), ¬(v = FALSE) ⊢ P  ⟹  H ⊢ (v = TRUE) ⇒ P
symbol BOOL11 [H v P]
  : (((H ∷ (v = BTRUE)) ∷ (¬ (v = BFALSE))) ⊩ P)
  → (H ⊩ (v = BTRUE) ⇒ P);

// BOOL12: H, (v = FALSE), ¬(v = TRUE) ⊢ P  ⟹  H ⊢ (v = FALSE) ⇒ P
symbol BOOL12 [H v P]
  : (((H ∷ (v = BFALSE)) ∷ (¬ (v = BTRUE))) ⊩ P)
  → (H ⊩ (v = BFALSE) ⇒ P);

// BOOL21: H ⊢ (v = TRUE) ⇒ P  ⟹  H ⊢ (TRUE = v) ⇒ P
symbol BOOL21 [H v P]
  : (H ⊩ (v = BTRUE) ⇒ P)
  → (H ⊩ (BTRUE = v) ⇒ P);

// BOOL22: H ⊢ (v = FALSE) ⇒ P  ⟹  H ⊢ (FALSE = v) ⇒ P
symbol BOOL22 [H v P]
  : (H ⊩ (v = BFALSE) ⇒ P)
  → (H ⊩ (BFALSE = v) ⇒ P);

// BOOL31: H ⊢ (v = FALSE) ⇒ P  ⟹  H ⊢ ¬(v = TRUE) ⇒ P
symbol BOOL31 [H v P]
  : (H ⊩ (v = BFALSE) ⇒ P)
  → (H ⊩ ¬ (v = BTRUE) ⇒ P);

// BOOL32: H ⊢ (v = TRUE) ⇒ P  ⟹  H ⊢ ¬(v = FALSE) ⇒ P
symbol BOOL32 [H v P]
  : (H ⊩ (v = BTRUE) ⇒ P)
  → (H ⊩ ¬ (v = BFALSE) ⇒ P);

// BOOL41: H ⊢ (v = FALSE) ⇒ P  ⟹  H ⊢ ¬(TRUE = v) ⇒ P
symbol BOOL41 [H v P]
  : (H ⊩ (v = BFALSE) ⇒ P)
  → (H ⊩ ¬ (BTRUE = v) ⇒ P);

// BOOL42: H ⊢ (v = TRUE) ⇒ P  ⟹  H ⊢ ¬(FALSE = v) ⇒ P
symbol BOOL42 [H v P]
  : (H ⊩ (v = BTRUE) ⇒ P)
  → (H ⊩ ¬ (BFALSE = v) ⇒ P);

// BOOL51: H ⊢ (TRUE = FALSE) ⇒ P  (no antecedents)
symbol BOOL51 [H P] : H ⊩ (BTRUE = BFALSE) ⇒ P;

// BOOL52: H ⊢ ¬(FALSE = TRUE) ⇒ P  (no antecedents)
symbol BOOL52 [H P] : H ⊩ ¬ (BFALSE = BTRUE) ⇒ P;

// ---- primed (result-producing) variants ----------------

symbol BOOL51' [H P] : Res (H ⟝ (BTRUE = BFALSE) ⇒ P)
≔ result TRUE;

symbol BOOL52' [H P] : Res (H ⟝ ¬ (BFALSE = BTRUE) ⇒ P)
≔ result TRUE;

// BOOL11': special — (H, (v=TRUE), ¬(v=FALSE) ⊢ P) ⇝ R
//   → result = (v = TRUE) ⇒ R
symbol BOOL11' [H v P]
  : Res (((H ∷ (v = BTRUE)) ∷ (¬ (v = BFALSE))) ⟝ P)
  → Res (H ⟝ (v = BTRUE) ⇒ P)
≔ λ ρ, result ((v = BTRUE) ⇒ obtain ρ);

// BOOL12': special — same pattern as BOOL11'.
symbol BOOL12' [H v P]
  : Res (((H ∷ (v = BFALSE)) ∷ (¬ (v = BTRUE))) ⟝ P)
  → Res (H ⟝ (v = BFALSE) ⇒ P)
≔ λ ρ, result ((v = BFALSE) ⇒ obtain ρ);

// BOOL21': Schema 1.
symbol BOOL21' [H v P]
  : Res (H ⟝ (v = BTRUE) ⇒ P)
  → Res (H ⟝ (BTRUE = v) ⇒ P)
≔ λ ρ, result (obtain ρ);

// BOOL22': Schema 1.
symbol BOOL22' [H v P]
  : Res (H ⟝ (v = BFALSE) ⇒ P)
  → Res (H ⟝ (BFALSE = v) ⇒ P)
≔ λ ρ, result (obtain ρ);

// BOOL31': Schema 1.
symbol BOOL31' [H v P]
  : Res (H ⟝ (v = BFALSE) ⇒ P)
  → Res (H ⟝ ¬ (v = BTRUE) ⇒ P)
≔ λ ρ, result (obtain ρ);

// BOOL32': Schema 1.
symbol BOOL32' [H v P]
  : Res (H ⟝ (v = BTRUE) ⇒ P)
  → Res (H ⟝ ¬ (v = BFALSE) ⇒ P)
≔ λ ρ, result (obtain ρ);

// BOOL41': Schema 1.
symbol BOOL41' [H v P]
  : Res (H ⟝ (v = BFALSE) ⇒ P)
  → Res (H ⟝ ¬ (BTRUE = v) ⇒ P)
≔ λ ρ, result (obtain ρ);

// BOOL42': Schema 1.
symbol BOOL42' [H v P]
  : Res (H ⟝ (v = BTRUE) ⇒ P)
  → Res (H ⟝ ¬ (BFALSE = v) ⇒ P)
≔ λ ρ, result (obtain ρ);
