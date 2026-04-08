// TRUE / FALSE (§A.9), STOP (§A.10), INS (§A.11)
require open
  pp2lp.B pp2lp.Proof;

// ---- TRUE (§A.9) ----

symbol VR1 [H R]
  : ▷ (H ⟝ ¬ TRUE ⇒ R);

symbol VR2 [H]
  : ▷ (H ⟝ FALSE)
  → ▷ (H ⟝ ¬ TRUE);

symbol VR3 [H R]
  : ▷ (H ⟝ R)
  → ▷ (H ⟝ TRUE ⇒ R);

symbol VR4 [H]
  : ▷ (H ⟝ TRUE);

// ---- FALSE ----

symbol FX1 [H R]
  : ▷ (H ⟝ R)
  → ▷ (H ⟝ ¬ FALSE ⇒ R);

symbol FX2 [H]
  : ▷ (H ⟝ ¬ FALSE);

symbol FX3 [H R]
  : ▷ (H ⟝ FALSE ⇒ R);

// ---- STOP (§A.10) ----

symbol STOP [H P]
  : ▷ (H ⟝ ¬ P ⇒ FALSE)
  → ▷ (H ⟝ P);

// ---- INS (§A.11) ----

symbol INS [H P]
  : ▷ (H ⟝ P ⇒ FALSE)
  → ▷ (H ⟝ FALSE);

// ---- Primed variants ----

// STOP′: base case. Result = the proved predicate itself.
symbol STOP_1 [H] [P : Prd]
  : Res (H ⟝ P);
rule obtain (STOP_1 [_] [$P]) ↪ $P;

symbol VR1_1 [H R]
  : Res (H ⟝ ¬ TRUE ⇒ R);
rule obtain (VR1_1) ↪ TRUE;

symbol VR4_1 [H]
  : Res (H ⟝ TRUE);
rule obtain (VR4_1) ↪ TRUE;

symbol FX2_1 [H]
  : Res (H ⟝ ¬ FALSE);
rule obtain (FX2_1) ↪ TRUE;

symbol FX3_1 [H R]
  : Res (H ⟝ FALSE ⇒ R);
rule obtain (FX3_1) ↪ TRUE;

symbol VR2_1 [H]
  : Res (H ⟝ FALSE)
  → Res (H ⟝ ¬ TRUE);
rule obtain (VR2_1 $r) ↪ obtain $r;

symbol VR3_1 [H R]
  : Res (H ⟝ R)
  → Res (H ⟝ TRUE ⇒ R);
rule obtain (VR3_1 $r) ↪ obtain $r;

symbol FX1_1 [H R]
  : Res (H ⟝ R)
  → Res (H ⟝ ¬ FALSE ⇒ R);
rule obtain (FX1_1 $r) ↪ obtain $r;
