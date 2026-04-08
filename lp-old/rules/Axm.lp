// Axiom rules (§A.6)
require open
  pp2lp.B pp2lp.Eq
  pp2lp.Subst pp2lp.Proof
  pp2lp.rules.Conj;

// ---- Base rules ----

symbol AXM1 [H P Q]
  : ⁇ (¬ P dans H)
  → ▷ (H ⟝ P ⇒ Q);

symbol AXM2 [H P Q]
  : ⁇ (P dans H)
  → ▷ (H ⟝ ¬ P ⇒ Q);

symbol AXM3 [H P]
  : ⁇ (P dans H)
  → ▷ (H ⟝ P);

symbol AXM4 [H P R]
  : ⁇ (R dans H)
  → ▷ (H ⟝ P ⇒ R);

symbol AXM5 [H P Q R]
  : ⁇ (¬ Q dans H)
  → ▷ (H ⟝ P ⇒ (Q ⇒ R));

symbol AXM6 [H P Q R]
  : ⁇ (Q dans H)
  → ▷ (H ⟝ P ⇒ (¬ Q ⇒ R));

symbol AXM7 [H P]
  : ▷ (H ⟝ P ⇒ P);

symbol AXM8 [H C R]
  : ⁇ (C contient R)
  → ▷ (H ⟝ C ⇒ R);

// AXM9: uses vpsub to handle both simple and compound Var.
symbol AXM9 [H] (x : Var) (E : Exp) (P : Prd) [R : Prd] [Q]
  : ⁇ (∀ x (¬ (TRUE ∧ P)) dans H)
  → ⁇ (prd_eq (vpsub x E P) R)
  → ▷ (H ⟝ R ⇒ Q);

// ---- Primed variants ----

symbol AXM1_1 [H P Q]
  : ⁇ (¬ P dans H)
  → Res (H ⟝ P ⇒ Q);
rule obtain (AXM1_1 _) ↪ TRUE;

symbol AXM2_1 [H P Q]
  : ⁇ (P dans H)
  → Res (H ⟝ ¬ P ⇒ Q);
rule obtain (AXM2_1 _) ↪ TRUE;

symbol AXM3_1 [H P]
  : ⁇ (P dans H)
  → Res (H ⟝ P);
rule obtain (AXM3_1 _) ↪ TRUE;

symbol AXM4_1 [H P R]
  : ⁇ (R dans H)
  → Res (H ⟝ P ⇒ R);
rule obtain (AXM4_1 _) ↪ TRUE;

symbol AXM5_1 [H P Q R]
  : ⁇ (¬ Q dans H)
  → Res (H ⟝ P ⇒ (Q ⇒ R));
rule obtain (AXM5_1 _) ↪ TRUE;

symbol AXM6_1 [H P Q R]
  : ⁇ (Q dans H)
  → Res (H ⟝ P ⇒ (¬ Q ⇒ R));
rule obtain (AXM6_1 _) ↪ TRUE;

symbol AXM7_1 [H P]
  : Res (H ⟝ P ⇒ P);
rule obtain (AXM7_1) ↪ TRUE;

symbol AXM8_1 [H C R]
  : ⁇ (C contient R)
  → Res (H ⟝ C ⇒ R);
rule obtain (AXM8_1 _) ↪ TRUE;

symbol AXM9_1 [H] [x : Var] [E : Exp] [P : Prd] [R : Prd] [Q]
  : ⁇ (∀ x (¬ (TRUE ∧ P)) dans H)
  → ⁇ (prd_eq (vpsub x E P) R)
  → Res (H ⟝ R ⇒ Q);
rule obtain (AXM9_1 [_] [_] [_] [_] [_] [_] _ _) ↪ TRUE;
