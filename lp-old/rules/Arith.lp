// Arithmetic (§A.14)
require open
  pp2lp.B pp2lp.Eq
  pp2lp.Proof;

// ---- Base rules ----

symbol AR1 [H E R]
  : ▷ (H ⟝ R)
  → ▷ (H ⟝ (E ≤ E) ⇒ R);

// FIXME. missing side cond:
// "a, b est numeriue"
symbol AR2 [H a b R]
  : ▷ (H ⟝ (a ≤ b) ⇒ R);

symbol AR3 [H a R]
  : ▷ (H ⟝ ((𝟏 - a) ≤ 𝟎) ⇒ R)
  → ▷ (H ⟝ ¬ (a ≤ 𝟎) ⇒ R);

// AR3 variant where solver provides simplified F = 1-a
symbol AR3_F [H] [a F : Exp] [R]
  : ⁇ (exp_eq (𝟏 - a) F)
  → ▷ (H ⟝ (F ≤ 𝟎) ⇒ R)
  → ▷ (H ⟝ ¬ (a ≤ 𝟎) ⇒ R);

// FIXME. missing side cond
// "E+F > 0"
symbol AR4 [H E F R]
  : ⁇ ((F ≤ 𝟎) dans H)
  → ▷ (H ⟝ (E ≤ 𝟎) ⇒ R);

symbol AR5 [H a R]
  : ⁇ ((a ≪ 𝟎) dans H)
  → ▷ (H ⟝ (a ≃ 𝟎) ⇒ ((⨪ a ≃ 𝟎) ⇒ R))
  → ▷ (H ⟝ (⨪ a ≤ 𝟎) ⇒ R);

symbol AR6 [H a R]
  : ⁇ ((⨪ a ≪ 𝟎) dans H)
  → ▷ (H ⟝ (a ≃ 𝟎) ⇒ ((a ≃ 𝟎) ⇒ R))
  → ▷ (H ⟝ (a ≤ 𝟎) ⇒ R);

// FIXME. missing side cond: "a + c = 0"
symbol AR7 [H a b c R]
  : ⁇ (((c + b) ≪ 𝟎) dans H)
  → ▷ (H ⟝ (a ≃ b) ⇒ (((a - b) ≤ 𝟎) ⇒ R))
  → ▷ (H ⟝ ((a - b) ≤ 𝟎) ⇒ R);

  // FIXME. missing side cond: "a + c = 0"
symbol AR8 [H a b c R]
  : ⁇ (((a - b) ≪ 𝟎) dans H)
  → ▷ (H ⟝ (b ≃ a) ⇒ (((c + b) ≪ 𝟎) ⇒ R))
  → ▷ (H ⟝ ((c + b) ≤ 𝟎) ⇒ R);

// FIXME. missing side cond "solveur(E) = F"
symbol AR9 [H E F R]
  : ▷ (H ⟝ (F ≤ 𝟎) ⇒ R)
  → ▷ (H ⟝ (E ≤ 𝟎) ⇒ R);

// FIXME. missing side cond "solveur(E) = F"
symbol AR10 [H P Q R]
  : ▷ (H ⟝ Q ⇒ R)
  → ▷ (H ⟝ P ⇒ R);

symbol AR11 [H x P]
  : ▷ (H ⟝ ¬ (x ≤ x) ⇒ P);

symbol AR12 [H a b P]
  : ▷ (((a ≤ b) ∷ H) ⟝ P)
  → ▷ (H ⟝ (a ≪ b) ⇒ P);

symbol AR5_2 [H a]
  : ⁇ ((a ≪ 𝟎) dans H)
  → ▷ (H ⟝ (a ≃ 𝟎) ⇒ ¬ (⨪ a ≪ 𝟎))
  → ▷ (H ⟝ ¬ (⨪ a ≤ 𝟎));

symbol AR6_2 [H a]
  : ⁇ ((⨪ a ≤ 𝟎) dans H)
  → ▷ (H ⟝ (a ≃ 𝟎) ⇒ ¬ (a ≪ 𝟎))
  → ▷ (H ⟝ ¬ (a ≤ 𝟎));

symbol AR7_2 [H a b c]
  : ⁇ (((c + b) ≤ 𝟎) dans H)
  → ▷ (H ⟝ (b ≃ a) ⇒ ¬ ((a - b) ≪ 𝟎))
  → ▷ (H ⟝ ¬ ((a - b) ≤ 𝟎));

symbol AR8_2 [H a b c]
  : ⁇ (((a - b) ≤ 𝟎) dans H)
  → ▷ (H ⟝ (b ≃ a) ⇒ ¬ ((c + b) ≪ 𝟎))
  → ▷ (H ⟝ ¬ ((c + b) ≤ 𝟎));

symbol AR13 [H] [a b : Exp]
  : ⁇ (exp_eq (𝟏 - a) b)
  → ▷ (H ⟝ b ≤ 𝟎)
  → ▷ (H ⟝ ¬ (a ≪ 𝟎));

// ---- Primed variants ----

// Schema 1 (1 antecedent)
symbol AR1_1 [H E R]
  : Res (H ⟝ R)
  → Res (H ⟝ (E ≤ E) ⇒ R);
rule obtain (AR1_1 $r) ↪ obtain $r;

// Schema 0 (no antecedents)
symbol AR2_1 [H a b R]
  : Res (H ⟝ (a ≤ b) ⇒ R);
rule obtain (AR2_1) ↪ TRUE;

// Schema 1
symbol AR3_1 [H a R]
  : Res (H ⟝ ((𝟏 - a) ≤ 𝟎) ⇒ R)
  → Res (H ⟝ ¬ (a ≤ 𝟎) ⇒ R);
rule obtain (AR3_1 $r) ↪ obtain $r;

// Schema 1
symbol AR3_F_1 [H] [a F : Exp] [R]
  : ⁇ (exp_eq (𝟏 - a) F)
  → Res (H ⟝ (F ≤ 𝟎) ⇒ R)
  → Res (H ⟝ ¬ (a ≤ 𝟎) ⇒ R);
rule obtain (AR3_F_1 _ $r) ↪ obtain $r;

// Schema 0
symbol AR4_1 [H E F R]
  : ⁇ ((F ≤ 𝟎) dans H)
  → Res (H ⟝ (E ≤ 𝟎) ⇒ R);
rule obtain (AR4_1 _) ↪ TRUE;

// Schema 1
symbol AR5_1 [H a R]
  : ⁇ ((a ≤ 𝟎) dans H)
  → Res (H ⟝ (⨪ a ≪ 𝟎) ⇒ ((a ≃ 𝟎) ⇒ R))
  → Res (H ⟝ (⨪ a ≤ 𝟎) ⇒ R);
rule obtain (AR5_1 _ $r) ↪ obtain $r;

// Schema 1
symbol AR6_1 [H a R]
  : ⁇ ((⨪ a ≤ 𝟎) dans H)
  → Res (H ⟝ (a ≪ 𝟎) ⇒ ((a ≃ 𝟎) ⇒ R))
  → Res (H ⟝ (a ≤ 𝟎) ⇒ R);
rule obtain (AR6_1 _ $r) ↪ obtain $r;

// Schema 1
symbol AR7_1 [H a b c R]
  : ⁇ (((c + b) ≤ 𝟎) dans H)
  → Res (H ⟝ (b ≃ a) ⇒ (((a - b) ≪ 𝟎) ⇒ R))
  → Res (H ⟝ ((a - b) ≤ 𝟎) ⇒ R);
rule obtain (AR7_1 _ $r) ↪ obtain $r;

// Schema 1
symbol AR8_1 [H a b c R]
  : ⁇ (((a - b) ≤ 𝟎) dans H)
  → Res (H ⟝ (b ≃ a) ⇒ (((c + b) ≪ 𝟎) ⇒ R))
  → Res (H ⟝ ((c + b) ≤ 𝟎) ⇒ R);
rule obtain (AR8_1 _ $r) ↪ obtain $r;

// Schema 1
symbol AR9_1 [H E F R]
  : Res (H ⟝ (F ≤ 𝟎) ⇒ R)
  → Res (H ⟝ (E ≤ 𝟎) ⇒ R);
rule obtain (AR9_1 $r) ↪ obtain $r;

// Schema 0 (no antecedents)
symbol AR11_1 [H x P]
  : Res (H ⟝ ¬ (x ≤ x) ⇒ P);
rule obtain (AR11_1) ↪ TRUE;

// Schema 1
symbol AR12_1 [H a b P]
  : Res (((a ≤ b) ∷ H) ⟝ P)
  → Res (H ⟝ (a ≪ b) ⇒ P);
rule obtain (AR12_1 $r) ↪ obtain $r;

// Schema 1
symbol AR13_1 [H] [a b : Exp]
  : ⁇ (exp_eq (𝟏 - a) b)
  → Res (H ⟝ b ≤ 𝟎)
  → Res (H ⟝ ¬ (a ≪ 𝟎));
rule obtain (AR13_1 _ $r) ↪ obtain $r;

// Schema 1
symbol AR5_2_1 [H a]
  : ⁇ ((a ≤ 𝟎) dans H)
  → Res (H ⟝ (a ≃ 𝟎) ⇒ ¬ (⨪ a ≪ 𝟎))
  → Res (H ⟝ ¬ (⨪ a ≤ 𝟎));
rule obtain (AR5_2_1 _ $r) ↪ obtain $r;

// Schema 1
symbol AR6_2_1 [H a]
  : ⁇ ((⨪ a ≤ 𝟎) dans H)
  → Res (H ⟝ (a ≃ 𝟎) ⇒ ¬ (a ≪ 𝟎))
  → Res (H ⟝ ¬ (a ≤ 𝟎));
rule obtain (AR6_2_1 _ $r) ↪ obtain $r;

// Schema 1
symbol AR7_2_1 [H a b c]
  : ⁇ (((c + b) ≤ 𝟎) dans H)
  → Res (H ⟝ (b ≃ a) ⇒ ¬ ((a - b) ≪ 𝟎))
  → Res (H ⟝ ¬ ((a - b) ≤ 𝟎));
rule obtain (AR7_2_1 _ $r) ↪ obtain $r;

// Schema 1
symbol AR8_2_1 [H a b c]
  : ⁇ (((a - b) ≤ 𝟎) dans H)
  → Res (H ⟝ (b ≃ a) ⇒ ¬ ((c + b) ≪ 𝟎))
  → Res (H ⟝ ¬ ((c + b) ≤ 𝟎));
rule obtain (AR8_2_1 _ $r) ↪ obtain $r;
