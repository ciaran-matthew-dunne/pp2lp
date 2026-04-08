// Negation (§A.5)
require open
  pp2lp.B pp2lp.Proof;

symbol NOT1 [H P R]
  : ▷ (H ⟝ P ⇒ R)
  → ▷ (H ⟝ ¬ ¬ P ⇒ R);

symbol NOT2 [H P]
  : ▷ (H ⟝ P)
  → ▷ (H ⟝ ¬ ¬ P);

// ---- Primed variants ----

symbol NOT1_1 [H P R]
  : Res (H ⟝ P ⇒ R)
  → Res (H ⟝ ¬ ¬ P ⇒ R);
rule obtain (NOT1_1 $r) ↪ obtain $r;

symbol NOT2_1 [H P]
  : Res (H ⟝ P)
  → Res (H ⟝ ¬ ¬ P);
rule obtain (NOT2_1 $r) ↪ obtain $r;
