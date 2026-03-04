// Rules on equalities (spec §A.13)
require open pp2lp.B pp2lp.Eq pp2lp.Interp;

// ---- reflexivity (EVR) ----------------

// EVR1: H ⊢ ¬(E = E) ⇒ P  (no antecedents)
symbol EVR1 [H E P] : H ⊩ ¬ (E = E) ⇒ P;

// EVR2: H ⊢ FALSE  ⟹  H ⊢ ¬(E = E)
symbol EVR2 [H E] : (H ⊩ FALSE) → (H ⊩ ¬ (E = E));

// EVR3: H ⊢ P  ⟹  H ⊢ (E = E) ⇒ P
symbol EVR3 [H E P] : (H ⊩ P) → (H ⊩ (E = E) ⇒ P);

// EVR4: H ⊢ (E = E)  (no antecedents)
symbol EVR4 [H E] : H ⊩ E = E;

// EVR11: n, m numeric, n ≠ m  ⟹  H ⊢ (n = m) ⇒ P
symbol EVR11 [H n m P] : H ⊩ (n = m) ⇒ P;

// ---- commutativity (EAXM, EIMP) ----------------

// EAXM1: ¬(F = E) is in H  ⟹  H ⊢ (E = F) ⇒ P
symbol EAXM1 [H E F P]
  : ⁇ (¬ (F = E) dans H) → (H ⊩ (E = F) ⇒ P);

// EAXM2: (F = E) is in H  ⟹  H ⊢ ¬(E = F) ⇒ P
symbol EAXM2 [H E F P]
  : ⁇ ((F = E) dans H) → (H ⊩ ¬ (E = F) ⇒ P);

// EAXM31: (F = E) is in H  ⟹  H ⊢ (E = F)
symbol EAXM31 [H E F]
  : ⁇ ((F = E) dans H) → (H ⊩ E = F);

// EAXM32: ¬(F = E) is in H  ⟹  H ⊢ ¬(E = F)
symbol EAXM32 [H E F]
  : ⁇ (¬ (F = E) dans H) → (H ⊩ ¬ (E = F));

// EIMP51: ¬(F = E) is in H; H ⊢ P  ⟹  H ⊢ ¬(E = F) ⇒ P
symbol EIMP51 [H E F P]
  : ⁇ (¬ (F = E) dans H) → (H ⊩ P) → (H ⊩ ¬ (E = F) ⇒ P);

// EIMP52: (F = E) is in H; H ⊢ P  ⟹  H ⊢ (E = F) ⇒ P
symbol EIMP52 [H E F P]
  : ⁇ ((F = E) dans H) → (H ⊩ P) → (H ⊩ (E = F) ⇒ P);

// EAXM91: ∀x · ¬(TRUE ∧ p = q) is in H; ∃E. [x := E](q = p) reduces to (a = b)
//   ⟹  H ⊢ (a = b) ⇒ Q
symbol EAXM91 [H x p q a b Q]
  : ⁇ (∀ x (¬ (TRUE ∧ (p = q))) dans H)
  → (H ⊩ (a = b) ⇒ Q);

// EAXM92: ∀x · ¬(TRUE ∧ ¬(p = q)) is in H; ∃E. [x := E](q = p) reduces to (a = b)
//   ⟹  H ⊢ ¬(a = b) ⇒ Q
symbol EAXM92 [H x p q a b Q]
  : ⁇ (∀ x (¬ (TRUE ∧ ¬ (p = q))) dans H)
  → (H ⊩ ¬ (a = b) ⇒ Q);

// ---- one-point rules (OPR) ----------------

// OPR1: x variable; x not free in E; Q = [x := E] P; H ⊢ Q  ⟹  H ⊢ (x = E) ⇒ P
symbol OPR1 [H x E] [P Q : Prd]
  : ⁇ (enf x E)
  → ⁇ (psub x E P == Q)
  → (H ⊩ Q) → (H ⊩ (#var x = E) ⇒ P);

// OPR2: x variable; x not free in E; Q = [x := E] P; H ⊢ Q  ⟹  H ⊢ (E = x) ⇒ P
symbol OPR2 [H x E] [P Q : Prd]
  : ⁇ (enf x E)
  → ⁇ (psub x E P == Q)
  → (H ⊩ Q) → (H ⊩ (E = #var x) ⇒ P);

// ---- equality between pairs (EQC) ----------------

// EQC1: H ⊢ ¬(a = c) ∨ ¬(b = d) ⇒ P  ⟹  H ⊢ ¬((a,b) = (c,d)) ⇒ P
symbol EQC1 [H a b c d P]
  : (H ⊩ (¬ (a = c) ∨ ¬ (b = d)) ⇒ P)
  → (H ⊩ ¬ ((a ↦ b) = (c ↦ d)) ⇒ P);

// EQC2: H ⊢ (a = c) ∧ (b = d) ⇒ P  ⟹  H ⊢ ((a,b) = (c,d)) ⇒ P
symbol EQC2 [H a b c d P]
  : (H ⊩ ((a = c) ∧ (b = d)) ⇒ P)
  → (H ⊩ ((a ↦ b) = (c ↦ d)) ⇒ P);

// ---- set equality (EQS) ----------------

// EQS1: H ⊢ E = F ⇒ R  ⟹  H ⊢ eql_set(E, F) ⇒ R
symbol EQS1 [H E F R]
  : (H ⊩ (E = F) ⇒ R) → (H ⊩ eql_set E F ⇒ R);

// EQS2: H ⊢ FALSE ⇒ R  ⟹  H ⊢ ¬eql_set(E, F) ⇒ R
symbol EQS2 [H E F R]
  : (H ⊩ FALSE ⇒ R) → (H ⊩ ¬ (eql_set E F) ⇒ R);

// ---- contradictions due to equalities (ECTR) ----------------

symbol ECTR1 [H E F P]
  : (H ⊩ (E = F) ⇒ P);

symbol ECTR2 [H E F P]
  : (H ⊩ (F = E) ⇒ P);

symbol ECTR3 [H E F P Q]
  : ⁇ ((E = F) dans H)
  → (H ⊩ ¬ P ⇒ Q);

symbol ECTR4 [H E F P Q]
  : ⁇ ((F = E) dans H)
  → (H ⊩ ¬ P ⇒ Q);

symbol ECTR5 [H E F P Q]
  : ⁇ ((E = F) dans H)
  → (H ⊩ P ⇒ Q);

symbol ECTR6 [H E F P Q]
  : ⁇ ((F = E) dans H)
  → (H ⊩ P ⇒ Q);

// ---- primed (result-producing) variants ----------------

symbol EVR1' [H E P] : Res (H ⟝ ¬ (E = E) ⇒ P)
≔ result TRUE;

symbol EVR2' [H E] : Res (H ⟝ FALSE) → Res (H ⟝ ¬ (E = E))
≔ λ ρ, result (obtain ρ);

symbol EVR3' [H E P] : Res (H ⟝ P) → Res (H ⟝ (E = E) ⇒ P)
≔ λ ρ, result (obtain ρ);

symbol EVR4' [H E] : Res (H ⟝ E = E)
≔ result TRUE;

symbol EVR11' [H n m P] : Res (H ⟝ (n = m) ⇒ P)
≔ result TRUE;

symbol EAXM1' [H E F P] : ⁇ (¬ (F = E) dans H) → Res (H ⟝ (E = F) ⇒ P)
≔ λ _, result TRUE;

symbol EAXM2' [H E F P] : ⁇ ((F = E) dans H) → Res (H ⟝ ¬ (E = F) ⇒ P)
≔ λ _, result TRUE;

symbol EAXM31' [H E F] : ⁇ ((F = E) dans H) → Res (H ⟝ E = F)
≔ λ _, result TRUE;

symbol EAXM32' [H E F] : ⁇ (¬ (F = E) dans H) → Res (H ⟝ ¬ (E = F))
≔ λ _, result TRUE;

// EIMP5': Schema 1 (one antecedent: H ⊢ P).
symbol EIMP51' [H E F P]
  : ⁇ (¬ (F = E) dans H) → Res (H ⟝ P) → Res (H ⟝ ¬ (E = F) ⇒ P)
≔ λ _ ρ, result (obtain ρ);

symbol EIMP52' [H E F P]
  : ⁇ ((F = E) dans H) → Res (H ⟝ P) → Res (H ⟝ (E = F) ⇒ P)
≔ λ _ ρ, result (obtain ρ);

// EAXM91': Schema 0.
symbol EAXM91' [H x p q a b Q]
  : ⁇ (∀ x (¬ (TRUE ∧ (p = q))) dans H)
  → Res (H ⟝ (a = b) ⇒ Q)
≔ λ _, result TRUE;

// EAXM92': Schema 0.
symbol EAXM92' [H x p q a b Q]
  : ⁇ (∀ x (¬ (TRUE ∧ ¬ (p = q))) dans H)
  → Res (H ⟝ ¬ (a = b) ⇒ Q)
≔ λ _, result TRUE;

// OPR1': Schema 1.
symbol OPR1' [H x E] [P Q : Prd]
  : ⁇ (enf x E)
  → ⁇ (psub x E P == Q)
  → Res (H ⟝ Q) → Res (H ⟝ (#var x = E) ⇒ P)
≔ λ _ _ ρ, result (obtain ρ);

// OPR2': Schema 1.
symbol OPR2' [H x E] [P Q : Prd]
  : ⁇ (enf x E)
  → ⁇ (psub x E P == Q)
  → Res (H ⟝ Q) → Res (H ⟝ (E = #var x) ⇒ P)
≔ λ _ _ ρ, result (obtain ρ);

// EQC1': Schema 1.
symbol EQC1' [H a b c d P]
  : Res (H ⟝ (¬ (a = c) ∨ ¬ (b = d)) ⇒ P)
  → Res (H ⟝ ¬ ((a ↦ b) = (c ↦ d)) ⇒ P)
≔ λ ρ, result (obtain ρ);

// EQC2': Schema 1.
symbol EQC2' [H a b c d P]
  : Res (H ⟝ ((a = c) ∧ (b = d)) ⇒ P)
  → Res (H ⟝ ((a ↦ b) = (c ↦ d)) ⇒ P)
≔ λ ρ, result (obtain ρ);

// EQS1': Schema 1.
symbol EQS1' [H E F R]
  : Res (H ⟝ (E = F) ⇒ R) → Res (H ⟝ eql_set E F ⇒ R)
≔ λ ρ, result (obtain ρ);

// EQS2': Schema 1.
symbol EQS2' [H E F R]
  : Res (H ⟝ FALSE ⇒ R) → Res (H ⟝ ¬ (eql_set E F) ⇒ R)
≔ λ ρ, result (obtain ρ);

// ECTR1': Schema 0.
symbol ECTR1' [H E F P]
  : Res (H ⟝ (E = F) ⇒ P)
≔ result TRUE;

// ECTR2': Schema 0.
symbol ECTR2' [H E F P]
  : Res (H ⟝ (F = E) ⇒ P)
≔ result TRUE;

// ECTR3': Schema 0.
symbol ECTR3' [H E F P Q]
  : ⁇ ((E = F) dans H)
  → Res (H ⟝ ¬ P ⇒ Q)
≔ λ _, result TRUE;

// ECTR4': Schema 0.
symbol ECTR4' [H E F P Q]
  : ⁇ ((F = E) dans H)
  → Res (H ⟝ ¬ P ⇒ Q)
≔ λ _, result TRUE;

// ECTR5': Schema 0.
symbol ECTR5' [H E F P Q]
  : ⁇ ((E = F) dans H)
  → Res (H ⟝ P ⇒ Q)
≔ λ _, result TRUE;

// ECTR6': Schema 0.
symbol ECTR6' [H E F P Q]
  : ⁇ ((F = E) dans H)
  → Res (H ⟝ P ⇒ Q)
≔ λ _, result TRUE;
