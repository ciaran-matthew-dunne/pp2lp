// Implication (§A.3)
require open
  pp2lp.B pp2lp.Proof;

// ---- Base rules ----

symbol IMP1 [H P Q R]
  : ▷ (H ⟝ P ⇒ (¬ Q ⇒ R))
  → ▷ (H ⟝ ¬ (P ⇒ Q) ⇒ R);

symbol IMP2 [H P Q]
  : ▷ (H ⟝ ¬ Q)
  → ▷ (H ⟝ P)
  → ▷ (H ⟝ ¬ (P ⇒ Q));

symbol IMP3 [H P Q R]
  : ▷ (H ⟝ Q ⇒ R)
  → ▷ (H ⟝ (¬ P) ⇒ R)
  → ▷ (H ⟝ (P ⇒ Q) ⇒ R);

symbol IMP4 [H P Q]
  : ▷ ((P ∷ H) ⟝ Q)
  → ▷ (H ⟝ P ⇒ Q);

symbol IMP5 [H P Q]
  : ⁇ (P dans H)
  → ▷ (H ⟝ Q)
  → ▷ (H ⟝ P ⇒ Q);


// ---- Primed variants ----

// IMP4′: result = P ⇒ R.
symbol IMP4_1 [H] [P : Prd] [Q]
  : Res ((P ∷ H) ⟝ Q)
  → Res (H ⟝ (P ⇒ Q));
rule obtain (IMP4_1 [_] [$P] [_] $r) ↪ $P ⇒ obtain $r;

symbol IMP1_1 [H P Q R]
  : Res (H ⟝ P ⇒ (¬ Q ⇒ R))
  → Res (H ⟝ ¬ (P ⇒ Q) ⇒ R);
rule obtain (IMP1_1 $r) ↪ obtain $r;

symbol IMP5_1 [H P Q]
  : ⁇ (P dans H)
  → Res (H ⟝ Q)
  → Res (H ⟝ P ⇒ Q);
rule obtain (IMP5_1 _ $r) ↪ obtain $r;

symbol IMP2_1 [H P Q]
  : Res (H ⟝ ¬ Q)
  → Res (H ⟝ P)
  → Res (H ⟝ ¬ (P ⇒ Q));
rule obtain (IMP2_1 $r $s) ↪ (obtain $r) ∧ (obtain $s);

symbol IMP3_1 [H P Q R]
  : Res (H ⟝ Q ⇒ R)
  → Res (H ⟝ (¬ P) ⇒ R)
  → Res (H ⟝ (P ⇒ Q) ⇒ R);
rule obtain (IMP3_1 $r $s) ↪ (obtain $r) ∧ (obtain $s);
