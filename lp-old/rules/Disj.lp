// Disjunction (§A.2)
require open
  pp2lp.B pp2lp.Proof;

// ---- Base rules ----

symbol OR1 [H P Q R]
  : ▷ (H ⟝ ¬ P ⇒ (¬ Q ⇒ R))
  → ▷ (H ⟝ ¬ (P ∨ Q) ⇒ R);

symbol OR2 [H P Q]
  : ▷ (H ⟝ ¬ Q)
  → ▷ (H ⟝ ¬ P)
  → ▷ (H ⟝ ¬ (P ∨ Q));

symbol OR3 [H P Q R]
  : ▷ (H ⟝ Q ⇒ R)
  → ▷ (H ⟝ P ⇒ R)
  → ▷ (H ⟝ (P ∨ Q) ⇒ R);

symbol OR4 [H P Q]
  : ▷ (H ⟝ ¬ P ⇒ Q)
  → ▷ (H ⟝ P ∨ Q);

// ---- Primed variants ----

symbol OR1_1 [H P Q R]
  : Res (H ⟝ ¬ P ⇒ (¬ Q ⇒ R))
  → Res (H ⟝ ¬ (P ∨ Q) ⇒ R);
rule obtain (OR1_1 $r) ↪ obtain $r;

symbol OR4_1 [H P Q]
  : Res (H ⟝ ¬ P ⇒ Q)
  → Res (H ⟝ P ∨ Q);
rule obtain (OR4_1 $r) ↪ obtain $r;

symbol OR2_1 [H P Q]
  : Res (H ⟝ ¬ Q)
  → Res (H ⟝ ¬ P)
  → Res (H ⟝ ¬ (P ∨ Q));
rule obtain (OR2_1 $r $s) ↪ (obtain $r) ∧ (obtain $s);

symbol OR3_1 [H P Q R]
  : Res (H ⟝ Q ⇒ R)
  → Res (H ⟝ P ⇒ R)
  → Res (H ⟝ (P ∨ Q) ⇒ R);
rule obtain (OR3_1 $r $s) ↪ (obtain $r) ∧ (obtain $s);
