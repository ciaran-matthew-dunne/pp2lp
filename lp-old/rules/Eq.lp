// Equality (§A.13)
require open
  pp2lp.B pp2lp.Eq
  pp2lp.NonFree pp2lp.Subst
  pp2lp.Proof;

// ---- EVR (equality reflexivity) ----

symbol EVR1 [H E P]
  : ▷ (H ⟝ ¬ (E ≃ E) ⇒ P);

// FIXME. missing side cond:
// "n,m ∈ ℕ. n,m distinct."
symbol EVR11 [H n m P]
  : ▷ (H ⟝ (n ≃ m) ⇒ P);

symbol EVR2 [H E]
  : ▷ (H ⟝ FALSE)
  → ▷ (H ⟝ ¬ (E ≃ E));

symbol EVR3 [H E P]
  : ▷ (H ⟝ P)
  → ▷ (H ⟝ (E ≃ E) ⇒ P);

symbol EVR4 [H E]
  : ▷ (H ⟝ E ≃ E);

// ---- EAXM (equality axioms) ----

symbol EAXM1 [H E F P]
  : ⁇ (¬ (F ≃ E) dans H)
  → ▷ (H ⟝ (E ≃ F) ⇒ P);

symbol EAXM2 [H E F P]
  : ⁇ ((F ≃ E) dans H)
  → ▷ (H ⟝ ¬ (E ≃ F) ⇒ P);

symbol EAXM31 [H E F]
  : ⁇ ((F ≃ E) dans H)
  → ▷ (H ⟝ E ≃ F);

symbol EAXM32 [H E F]
  : ⁇ (¬ (F ≃ E) dans H)
  → ▷ (H ⟝ ¬ (E ≃ F));

symbol EIMP51 [H E F P]
  : ⁇ (¬ (F ≃ E) dans H)
  → ▷ (H ⟝ P)
  → ▷ (H ⟝ ¬ (E ≃ F) ⇒ P);

symbol EIMP52 [H E F P]
  : ⁇ ((F ≃ E) dans H)
  → ▷ (H ⟝ P)
  → ▷ (H ⟝ (E ≃ F) ⇒ P);

// FIXME. missing side cond
// "[x := E](q = p) reduces to (a = b)"
symbol EAXM91 [H x p q a b Q]
  : ⁇ (∀ x (¬ (TRUE ∧ (p ≃ q))) dans H)
  → ▷ (H ⟝ (a ≃ b) ⇒ Q);

// FIXME. missing side cond
// "[x := E](q = p) reduces to (a = b)"
symbol EAXM92 [H x p q a b Q]
  : ⁇ (∀ x (¬ (TRUE ∧ ¬ (p ≃ q))) dans H)
  → ▷ (H ⟝ ¬ (a ≃ b) ⇒ Q);

// ---- OPR (substitution from equality) ----

// FIXME. missing side cond:
// "x not free in H".
// FIXME. x should be var not string.
symbol OPR1 [H] [x : String] [E] [P : Prd]
  : ⁇ (venf x E)
  → ▷ (H ⟝ vpsub x E P)
  → ▷ (H ⟝ (eid x ≃ E) ⇒ P);

// FIXME. missing side cond:
// "x not free in H".
// FIXME. x should be var not string.
symbol OPR2 [H] [x : String] [E] [P : Prd]
  : ⁇ (enf x E)
  → ▷ (H ⟝ psub x E P)
  → ▷ (H ⟝ (E ≃ eid x) ⇒ P);

// ---- EQC (pair equality) ----

symbol EQC1 [H a b c d P]
  : ▷ (H ⟝ (¬ (a ≃ c) ∨ ¬ (b ≃ d)) ⇒ P)
  → ▷ (H ⟝ ¬ ((a ↦ b) ≃ (c ↦ d)) ⇒ P);

symbol EQC2 [H a b c d P]
  : ▷ (H ⟝ ((a ≃ c) ∧ (b ≃ d)) ⇒ P)
  → ▷ (H ⟝ ((a ↦ b) ≃ (c ↦ d)) ⇒ P);

// ---- EQS (set equality) ----

symbol EQS1 [H E F R]
  : ▷ (H ⟝ (E ≃ F) ⇒ R)
  → ▷ (H ⟝ eql_set E F ⇒ R);

symbol EQS2 [H E F R]
  : ▷ (H ⟝ FALSE ⇒ R)
  → ▷ (H ⟝ ¬ (eql_set E F) ⇒ R);

// ---- ECTR (equality contradiction) ----

// FIXME. missing side cond:
// "le replcement de E pr F dns Q donne R"
symbol ECTR1 [H E F P Q R]
  : ⁇ (¬ Q dans H)
  → ⁇ (R dans H)
  → ▷ (H ⟝ (E ≃ F) ⇒ P);

// FIXME. missing side cond:
// "le replcement de E pr F dns Q donne R"
symbol ECTR2 [H E F P Q R]
  : ⁇ (¬ Q dans H)
  → ⁇ (R dans H)
  →  ▷ (H ⟝ (F ≃ E) ⇒ P);

// FIXME. missing side cond:
// "le replcement de E pr F dns Q donne R"
symbol ECTR3 [H E F P Q]
  : ⁇ ((E ≃ F) dans H)
  → ▷ (H ⟝ ¬ P ⇒ Q);

symbol ECTR4 [H E F P Q]
  : ⁇ ((F ≃ E) dans H)
  → ▷ (H ⟝ ¬ P ⇒ Q);

symbol ECTR5 [H E F P Q]
  : ⁇ ((E ≃ F) dans H)
  → ▷ (H ⟝ P ⇒ Q);

symbol ECTR6 [H E F P Q]
  : ⁇ ((F ≃ E) dans H)
  → ▷ (H ⟝ P ⇒ Q);

// ---- Primed variants ----

// Schema 0
symbol EVR1_1 [H E P]
  : Res (H ⟝ ¬ (E ≃ E) ⇒ P);
rule obtain (EVR1_1) ↪ TRUE;

// Schema 1
symbol EVR2_1 [H E]
  : Res (H ⟝ FALSE)
  → Res (H ⟝ ¬ (E ≃ E));
rule obtain (EVR2_1 $r) ↪ obtain $r;

// Schema 1
symbol EVR3_1 [H E P]
  : Res (H ⟝ P)
  → Res (H ⟝ (E ≃ E) ⇒ P);
rule obtain (EVR3_1 $r) ↪ obtain $r;

// Schema 0
symbol EVR4_1 [H E]
  : Res (H ⟝ E ≃ E);
rule obtain (EVR4_1) ↪ TRUE;

// Schema 0
symbol EVR11_1 [H n m P]
  : Res (H ⟝ (n ≃ m) ⇒ P);
rule obtain (EVR11_1) ↪ TRUE;

// Schema 0
symbol EAXM1_1 [H E F P]
  : ⁇ (¬ (F ≃ E) dans H)
  → Res (H ⟝ (E ≃ F) ⇒ P);
rule obtain (EAXM1_1 _) ↪ TRUE;

// Schema 0
symbol EAXM2_1 [H E F P]
  : ⁇ ((F ≃ E) dans H)
  → Res (H ⟝ ¬ (E ≃ F) ⇒ P);
rule obtain (EAXM2_1 _) ↪ TRUE;

// Schema 0
symbol EAXM31_1 [H E F]
  : ⁇ ((F ≃ E) dans H)
  → Res (H ⟝ E ≃ F);
rule obtain (EAXM31_1 _) ↪ TRUE;

// Schema 0
symbol EAXM32_1 [H E F]
  : ⁇ (¬ (F ≃ E) dans H)
  → Res (H ⟝ ¬ (E ≃ F));
rule obtain (EAXM32_1 _) ↪ TRUE;

// Schema 1
symbol EIMP51_1 [H E F P]
  : ⁇ (¬ (F ≃ E) dans H)
  → Res (H ⟝ P)
  → Res (H ⟝ ¬ (E ≃ F) ⇒ P);
rule obtain (EIMP51_1 _ $r) ↪ obtain $r;

// Schema 1
symbol EIMP52_1 [H E F P]
  : ⁇ ((F ≃ E) dans H)
  → Res (H ⟝ P)
  → Res (H ⟝ (E ≃ F) ⇒ P);
rule obtain (EIMP52_1 _ $r) ↪ obtain $r;

// Schema 0
symbol EAXM91_1 [H x p q a b Q]
  : ⁇ (∀ x (¬ (TRUE ∧ (p ≃ q))) dans H)
  → Res (H ⟝ (a ≃ b) ⇒ Q);
rule obtain (EAXM91_1 _) ↪ TRUE;

// Schema 0
symbol EAXM92_1 [H x p q a b Q]
  : ⁇ (∀ x (¬ (TRUE ∧ ¬ (p ≃ q))) dans H)
  → Res (H ⟝ ¬ (a ≃ b) ⇒ Q);
rule obtain (EAXM92_1 _) ↪ TRUE;

// Schema 1
symbol OPR1_1 [H] [x : String] [E] [P : Prd]
  : ⁇ (enf x E)
  → Res (H ⟝ psub x E P)
  → Res (H ⟝ (eid x ≃ E) ⇒ P);
rule obtain (OPR1_1 _ $r) ↪ obtain $r;

// Schema 1
symbol OPR2_1 [H] [x : String] [E] [P : Prd]
  : ⁇ (enf x E)
  → Res (H ⟝ psub x E P)
  → Res (H ⟝ (E ≃ eid x) ⇒ P);
rule obtain (OPR2_1 _ $r) ↪ obtain $r;

// Schema 1
symbol EQC1_1 [H a b c d P]
  : Res (H ⟝ (¬ (a ≃ c) ∨ ¬ (b ≃ d)) ⇒ P)
  → Res (H ⟝ ¬ ((a ↦ b) ≃ (c ↦ d)) ⇒ P);
rule obtain (EQC1_1 $r) ↪ obtain $r;

// Schema 1
symbol EQC2_1 [H a b c d P]
  : Res (H ⟝ ((a ≃ c) ∧ (b ≃ d)) ⇒ P)
  → Res (H ⟝ ((a ↦ b) ≃ (c ↦ d)) ⇒ P);
rule obtain (EQC2_1 $r) ↪ obtain $r;

// Schema 1
symbol EQS1_1 [H E F R]
  : Res (H ⟝ (E ≃ F) ⇒ R)
  → Res (H ⟝ eql_set E F ⇒ R);
rule obtain (EQS1_1 $r) ↪ obtain $r;

// Schema 1
symbol EQS2_1 [H E F R]
  : Res (H ⟝ FALSE ⇒ R)
  → Res (H ⟝ ¬ (eql_set E F) ⇒ R);
rule obtain (EQS2_1 $r) ↪ obtain $r;

// Schema 0
symbol ECTR1_1 [H E F P]
  : Res (H ⟝ (E ≃ F) ⇒ P);
rule obtain (ECTR1_1) ↪ TRUE;

// Schema 0
symbol ECTR2_1 [H E F P]
  : Res (H ⟝ (F ≃ E) ⇒ P);
rule obtain (ECTR2_1) ↪ TRUE;

// Schema 0
symbol ECTR3_1 [H E F P Q]
  : ⁇ ((E ≃ F) dans H)
  → Res (H ⟝ ¬ P ⇒ Q);
rule obtain (ECTR3_1 _) ↪ TRUE;

// Schema 0
symbol ECTR4_1 [H E F P Q]
  : ⁇ ((F ≃ E) dans H)
  → Res (H ⟝ ¬ P ⇒ Q);
rule obtain (ECTR4_1 _) ↪ TRUE;

// Schema 0
symbol ECTR5_1 [H E F P Q]
  : ⁇ ((E ≃ F) dans H)
  → Res (H ⟝ P ⇒ Q);
rule obtain (ECTR5_1 _) ↪ TRUE;

// Schema 0
symbol ECTR6_1 [H E F P Q]
  : ⁇ ((F ≃ E) dans H)
  → Res (H ⟝ P ⇒ Q);
rule obtain (ECTR6_1 _) ↪ TRUE;
