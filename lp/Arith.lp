// Arithmetic rules (spec §A.14)
require open pp2lp.B pp2lp.Eq pp2lp.Interp;

// ---- base rules ----------------

// AR1: H ⊢ R  ⟹  H ⊢ E ≤ E ⇒ R
symbol AR1 [H E R]
  : (H ⊩ R) → (H ⊩ (E ≤ E) ⇒ R);

// AR2: a, b numeric; a > b  ⟹  H ⊢ a ≤ b ⇒ R
symbol AR2 [H a b R]
  : H ⊩ (a ≤ b) ⇒ R;

// AR3: H ⊢ 1 − a ≤ 0 ⇒ R  ⟹  H ⊢ ¬(a ≤ 0) ⇒ R
symbol AR3 [H a R]
  : (H ⊩ ((𝟏 - a) ≤ 𝟎) ⇒ R) → (H ⊩ ¬ (a ≤ 𝟎) ⇒ R);

// AR4: F ≤ 0 ∈ H; E + F > 0  ⟹  H ⊢ E ≤ 0 ⇒ R
symbol AR4 [H E F R]
  : ⁇ ((F ≤ 𝟎) dans H)
  → (H ⊩ (E ≤ 𝟎) ⇒ R);

// AR5: a ≤ 0 ∈ H; H ⊢ −a ≪ 0 ⇒ (a = 0 ⇒ R)  ⟹  H ⊢ −a ≤ 0 ⇒ R
symbol AR5 [H a R]
  : ⁇ ((a ≤ 𝟎) dans H)
  → (H ⊩ (⨪ a ≪ 𝟎) ⇒ ((a = 𝟎) ⇒ R))
  → (H ⊩ (⨪ a ≤ 𝟎) ⇒ R);

// AR6: −a ≤ 0 ∈ H; H ⊢ a ≪ 0 ⇒ (a = 0 ⇒ R)  ⟹  H ⊢ a ≤ 0 ⇒ R
symbol AR6 [H a R]
  : ⁇ ((⨪ a ≤ 𝟎) dans H)
  → (H ⊩ (a ≪ 𝟎) ⇒ ((a = 𝟎) ⇒ R))
  → (H ⊩ (a ≤ 𝟎) ⇒ R);

// AR7: c + b ≤ 0 ∈ H; a + c = 0; H ⊢ b = a ⇒ (a − b ≪ 0 ⇒ R)
//   ⟹  H ⊢ a − b ≤ 0 ⇒ R
symbol AR7 [H a b c R]
  : ⁇ (((c + b) ≤ 𝟎) dans H)
  → (H ⊩ (b = a) ⇒ (((a - b) ≪ 𝟎) ⇒ R))
  → (H ⊩ ((a - b) ≤ 𝟎) ⇒ R);

// AR8: a − b ≤ 0 ∈ H; a + c = 0; H ⊢ b = a ⇒ (c + b ≪ 0 ⇒ R)
//   ⟹  H ⊢ c + b ≤ 0 ⇒ R
symbol AR8 [H a b c R]
  : ⁇ (((a - b) ≤ 𝟎) dans H)
  → (H ⊩ (b = a) ⇒ (((c + b) ≪ 𝟎) ⇒ R))
  → (H ⊩ ((c + b) ≤ 𝟎) ⇒ R);

// AR9: solver(E) = F; H ⊢ F ≤ 0 ⇒ R  ⟹  H ⊢ E ≤ 0 ⇒ R
symbol AR9 [H E F R]
  : (H ⊩ (F ≤ 𝟎) ⇒ R) → (H ⊩ (E ≤ 𝟎) ⇒ R);

// AR10: solver(P) = Q; H ⊢ Q ⇒ R  ⟹  H ⊢ P ⇒ R
symbol AR10 [H P Q R]
  : (H ⊩ Q ⇒ R) → (H ⊩ P ⇒ R);

// AR11: H ⊢ ¬(x ≤ x) ⇒ P  (no antecedents)
symbol AR11 [H x P] : H ⊩ ¬ (x ≤ x) ⇒ P;

// AR12: H, (a ≤ b) ⊢ P  ⟹  H ⊢ (a ≪ b) ⇒ P
symbol AR12 [H a b P]
  : ((H ∷ (a ≤ b)) ⊩ P) → (H ⊩ (a ≪ b) ⇒ P);

// ---- missing base rules (§10.3.3) ----------------

// AR5_2: a ≤ 0 ∈ H; H ⊢ a = 0 ⇒ ¬(−a ≪ 0)  ⟹  H ⊢ ¬(−a ≤ 0)
symbol AR5_2 [H a]
  : ⁇ ((a ≤ 𝟎) dans H)
  → (H ⊩ (a = 𝟎) ⇒ ¬ (⨪ a ≪ 𝟎))
  → (H ⊩ ¬ (⨪ a ≤ 𝟎));

// AR6_2: −a ≤ 0 ∈ H; H ⊢ a = 0 ⇒ ¬(a ≪ 0)  ⟹  H ⊢ ¬(a ≤ 0)
symbol AR6_2 [H a]
  : ⁇ ((⨪ a ≤ 𝟎) dans H)
  → (H ⊩ (a = 𝟎) ⇒ ¬ (a ≪ 𝟎))
  → (H ⊩ ¬ (a ≤ 𝟎));

// AR7_2: c + b ≤ 0 ∈ H; a + c = 0; H ⊢ b = a ⇒ ¬(a − b ≪ 0)
//   ⟹  H ⊢ ¬(a − b ≤ 0)
symbol AR7_2 [H a b c]
  : ⁇ (((c + b) ≤ 𝟎) dans H)
  → (H ⊩ (b = a) ⇒ ¬ ((a - b) ≪ 𝟎))
  → (H ⊩ ¬ ((a - b) ≤ 𝟎));

// AR8_2: a − b ≤ 0 ∈ H; a + c = 0; H ⊢ b = a ⇒ ¬(c + b ≪ 0)
//   ⟹  H ⊢ ¬(c + b ≤ 0)
symbol AR8_2 [H a b c]
  : ⁇ (((a - b) ≤ 𝟎) dans H)
  → (H ⊩ (b = a) ⇒ ¬ ((c + b) ≪ 𝟎))
  → (H ⊩ ¬ ((c + b) ≤ 𝟎));

// AR13: 1 − a = b; H ⊢ b ≤ 0  ⟹  H ⊢ ¬(a ≪ 0)
symbol AR13 [H] [a b : Exp]
  : ⁇ ((𝟏 - a) == b)
  → (H ⊩ b ≤ 𝟎)
  → (H ⊩ ¬ (a ≪ 𝟎));

// ---- primed (result-producing) variants ----------------

symbol AR1' [H E R] : Res (H ⟝ R) → Res (H ⟝ (E ≤ E) ⇒ R)
≔ λ ρ, result (obtain ρ);

symbol AR2' [H a b R] : Res (H ⟝ (a ≤ b) ⇒ R)
≔ result TRUE;

symbol AR3' [H a R]
  : Res (H ⟝ ((𝟏 - a) ≤ 𝟎) ⇒ R) → Res (H ⟝ ¬ (a ≤ 𝟎) ⇒ R)
≔ λ ρ, result (obtain ρ);

symbol AR4' [H E F R]
  : ⁇ ((F ≤ 𝟎) dans H)
  → Res (H ⟝ (E ≤ 𝟎) ⇒ R)
≔ λ _, result TRUE;

symbol AR5' [H a R]
  : ⁇ ((a ≤ 𝟎) dans H)
  → Res (H ⟝ (⨪ a ≪ 𝟎) ⇒ ((a = 𝟎) ⇒ R))
  → Res (H ⟝ (⨪ a ≤ 𝟎) ⇒ R)
≔ λ _ ρ, result (obtain ρ);

symbol AR6' [H a R]
  : ⁇ ((⨪ a ≤ 𝟎) dans H)
  → Res (H ⟝ (a ≪ 𝟎) ⇒ ((a = 𝟎) ⇒ R))
  → Res (H ⟝ (a ≤ 𝟎) ⇒ R)
≔ λ _ ρ, result (obtain ρ);

symbol AR7' [H a b c R]
  : ⁇ (((c + b) ≤ 𝟎) dans H)
  → Res (H ⟝ (b = a) ⇒ (((a - b) ≪ 𝟎) ⇒ R))
  → Res (H ⟝ ((a - b) ≤ 𝟎) ⇒ R)
≔ λ _ ρ, result (obtain ρ);

symbol AR8' [H a b c R]
  : ⁇ (((a - b) ≤ 𝟎) dans H)
  → Res (H ⟝ (b = a) ⇒ (((c + b) ≪ 𝟎) ⇒ R))
  → Res (H ⟝ ((c + b) ≤ 𝟎) ⇒ R)
≔ λ _ ρ, result (obtain ρ);

symbol AR9' [H E F R]
  : Res (H ⟝ (F ≤ 𝟎) ⇒ R) → Res (H ⟝ (E ≤ 𝟎) ⇒ R)
≔ λ ρ, result (obtain ρ);

symbol AR10' [H P Q R]
  : Res (H ⟝ Q ⇒ R) → Res (H ⟝ P ⇒ R)
≔ λ ρ, result (obtain ρ);

symbol AR11' [H x P] : Res (H ⟝ ¬ (x ≤ x) ⇒ P)
≔ result TRUE;

// AR12': special — (H, (a ≤ b) ⊢ P) ⇝ R → result = (a ≤ b) ⇒ R
symbol AR12' [H a b P]
  : Res ((H ∷ (a ≤ b)) ⟝ P) → Res (H ⟝ (a ≪ b) ⇒ P)
≔ λ ρ, result ((a ≤ b) ⇒ obtain ρ);

// AR5_2': Schema 1.
symbol AR5_2' [H a]
  : ⁇ ((a ≤ 𝟎) dans H)
  → Res (H ⟝ (a = 𝟎) ⇒ ¬ (⨪ a ≪ 𝟎))
  → Res (H ⟝ ¬ (⨪ a ≤ 𝟎))
≔ λ _ ρ, result (obtain ρ);

// AR6_2': Schema 1.
symbol AR6_2' [H a]
  : ⁇ ((⨪ a ≤ 𝟎) dans H)
  → Res (H ⟝ (a = 𝟎) ⇒ ¬ (a ≪ 𝟎))
  → Res (H ⟝ ¬ (a ≤ 𝟎))
≔ λ _ ρ, result (obtain ρ);

// AR7_2': Schema 1.
symbol AR7_2' [H a b c]
  : ⁇ (((c + b) ≤ 𝟎) dans H)
  → Res (H ⟝ (b = a) ⇒ ¬ ((a - b) ≪ 𝟎))
  → Res (H ⟝ ¬ ((a - b) ≤ 𝟎))
≔ λ _ ρ, result (obtain ρ);

// AR8_2': Schema 1.
symbol AR8_2' [H a b c]
  : ⁇ (((a - b) ≤ 𝟎) dans H)
  → Res (H ⟝ (b = a) ⇒ ¬ ((c + b) ≪ 𝟎))
  → Res (H ⟝ ¬ ((c + b) ≤ 𝟎))
≔ λ _ ρ, result (obtain ρ);

// AR13': Schema 1.
symbol AR13' [H] [a b : Exp]
  : ⁇ ((𝟏 - a) == b)
  → Res (H ⟝ b ≤ 𝟎)
  → Res (H ⟝ ¬ (a ≪ 𝟎))
≔ λ _ ρ, result (obtain ρ);
