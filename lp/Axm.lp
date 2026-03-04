// Axiom rules (spec §A.6)
require open pp2lp.B pp2lp.Eq pp2lp.Interp;

// ---- base rules ----------------

symbol AXM1 [H P Q] : ⁇ (¬ P dans H) → (H ⊩ P ⇒ Q);
symbol AXM2 [H P Q] : ⁇ (P dans H) → (H ⊩ ¬ P ⇒ Q);
symbol AXM3 [H P] : ⁇ (P dans H) → (H ⊩ P);
symbol AXM4 [H P R] : ⁇ (R dans H) → (H ⊩ P ⇒ R);
symbol AXM5 [H P Q R] : ⁇ (¬ Q dans H) → (H ⊩ P ⇒ (Q ⇒ R));
symbol AXM6 [H P Q R] : ⁇ (Q dans H) → (H ⊩ P ⇒ (¬ Q ⇒ R));
symbol AXM8 [H C R] : ⁇ (C contient R) → (H ⊩ C ⇒ R);

// AXM7 — identity axiom: H ⊢ P ⇒ P.
symbol AXM7 [H P] : H ⊩ P ⇒ P;

// AXM9 — contradiction via universal hypothesis instantiation.
// ∀x · ¬(TRUE ∧ P) is in H; ∃E. [x := E] P = R  ⟹  H ⊢ R ⇒ Q
symbol AXM9 [H x E] [P R : Prd] [Q]
  : ⁇ (∀ x (¬ (TRUE ∧ P)) dans H)
  → ⁇ (psub x E P == R)
  → (H ⊩ R ⇒ Q);

// ---- primed (result-producing) variants ----------------

// AXM rules: Schema 0.
symbol AXM1' [H P Q] : ⁇ (¬ P dans H) → Res (H ⟝ P ⇒ Q)
≔ λ _, result TRUE;

symbol AXM2' [H P Q] : ⁇ (P dans H) → Res (H ⟝ ¬ P ⇒ Q)
≔ λ _, result TRUE;

symbol AXM3' [H P] : ⁇ (P dans H) → Res (H ⟝ P)
≔ λ _, result TRUE;

symbol AXM4' [H P R] : ⁇ (R dans H) → Res (H ⟝ P ⇒ R)
≔ λ _, result TRUE;

symbol AXM5' [H P Q R] : ⁇ (¬ Q dans H) → Res (H ⟝ P ⇒ (Q ⇒ R))
≔ λ _, result TRUE;

symbol AXM6' [H P Q R] : ⁇ (Q dans H) → Res (H ⟝ P ⇒ (¬ Q ⇒ R))
≔ λ _, result TRUE;

symbol AXM7' [H P] : Res (H ⟝ P ⇒ P)
≔ result TRUE;

symbol AXM8' [H C R] : ⁇ (C contient R) → Res (H ⟝ C ⇒ R)
≔ λ _, result TRUE;

symbol AXM9' [H x E] [P R : Prd] [Q]
  : ⁇ (∀ x (¬ (TRUE ∧ P)) dans H)
  → ⁇ (psub x E P == R)
  → Res (H ⟝ R ⇒ Q)
≔ λ _ _, result TRUE;
