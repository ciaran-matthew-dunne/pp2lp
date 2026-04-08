// Equivalence (§A.4)
require open
  pp2lp.B pp2lp.Proof;

// ---- Base rules ----

symbol EQV1 [H P Q R]
  : ▷ (H ⟝ P ⇒ (¬ Q ⇒ R))
  → ▷ (H ⟝ ¬ P ⇒ (Q ⇒ R))
  → ▷ (H ⟝ ¬ (P ⇔ Q) ⇒ R);

symbol EQV2 [H P Q]
  : ▷ (H ⟝ P ⇒ ¬ Q)
  → ▷ (H ⟝ ¬ Q ⇒ P)
  → ▷ (H ⟝ ¬ (P ⇔ Q));

symbol EQV3 [H P Q R]
  : ▷ (H ⟝ P ⇒ (Q ⇒ R))
  → ▷ (H ⟝ ¬ P ⇒ (¬ Q ⇒ R))
  → ▷ (H ⟝ (P ⇔ Q) ⇒ R);

symbol EQV4 [H P Q]
  : ▷ (H ⟝ P ⇒ Q)
  → ▷ (H ⟝ Q ⇒ P)
  → ▷ (H ⟝ P ⇔ Q);

// ---- Primed variants ----

symbol EQV1_1 [H P Q R]
  : Res (H ⟝ P ⇒ (¬ Q ⇒ R))
  → Res (H ⟝ ¬ P ⇒ (Q ⇒ R))
  → Res (H ⟝ ¬ (P ⇔ Q) ⇒ R);
rule obtain (EQV1_1 $r $s) ↪ (obtain $r) ∧ (obtain $s);

symbol EQV2_1 [H P Q]
  : Res (H ⟝ P ⇒ ¬ Q)
  → Res (H ⟝ ¬ Q ⇒ P)
  → Res (H ⟝ ¬ (P ⇔ Q));
rule obtain (EQV2_1 $r $s) ↪ (obtain $r) ∧ (obtain $s);

symbol EQV3_1 [H P Q R]
  : Res (H ⟝ P ⇒ (Q ⇒ R))
  → Res (H ⟝ ¬ P ⇒ (¬ Q ⇒ R))
  → Res (H ⟝ (P ⇔ Q) ⇒ R);
rule obtain (EQV3_1 $r $s) ↪ (obtain $r) ∧ (obtain $s);

symbol EQV4_1 [H P Q]
  : Res (H ⟝ P ⇒ Q)
  → Res (H ⟝ Q ⇒ P)
  → Res (H ⟝ P ⇔ Q);
rule obtain (EQV4_1 $r $s) ↪ (obtain $r) ∧ (obtain $s);
