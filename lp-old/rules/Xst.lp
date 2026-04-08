// Existential quantification (§A.8)
require open
  pp2lp.B pp2lp.Eq
  pp2lp.NonFree pp2lp.Subst
  pp2lp.Proof;

// ---- Base rules ----

// Spec: "x and y are distinct".
symbol XST1 [H] [x y : Var] [P R]
  : ⁇ (vneq x y)
  → ▷ (H ⟝ ¬ (∃ (x ⨾ y) P) ⇒ R)
  → ▷ (H ⟝ ¬ (∃ x (∃ y P)) ⇒ R);

symbol XST2 [H] [x y : Var] [P]
  : ⁇ (vneq x y)
  → ▷ (H ⟝ ¬ (∃ (x ⨾ y) P))
  → ▷ (H ⟝ ¬ (∃ x (∃ y P)));

symbol XST3 [H] [x y : Var] [P R]
  : ⁇ (vneq x y)
  → ▷ (H ⟝ (∃ (x ⨾ y) P) ⇒ R)
  → ▷ (H ⟝ (∃ x (∃ y P)) ⇒ R);

symbol XST4 [H] [x y : Var] [P]
  : ⁇ (vneq x y)
  → ▷ (H ⟝ ∃ (x ⨾ y) P)
  → ▷ (H ⟝ ∃ x (∃ y P));

symbol XST5 [H x P R]
  : ▷ (H ⟝ (∀ x (¬ P)) ⇒ R)
  → ▷ (H ⟝ ¬ (∃ x P) ⇒ R);

symbol XST51 [H x P R]
  : ▷ (H ⟝ (∀ x P) ⇒ R)
  → ▷ (H ⟝ ¬ (∃ x (¬ P)) ⇒ R);

symbol XST6 [H x P]
  : ▷ (H ⟝ ∀ x (¬ P))
  → ▷ (H ⟝ ¬ (∃ x P));

symbol XST61 [H x P]
  : ▷ (H ⟝ ∀ x P)
  → ▷ (H ⟝ ¬ (∃ x (¬ P)));

symbol XST7 [H x P R]
  : ⁇ (vpnf x R)
  → ▷ (H ⟝ ∀ x (P ⇒ R))
  → ▷ (H ⟝ (∃ x P) ⇒ R);

// Spec: "x free in R; y free in
// neither P nor R; Q = [x:=y]P".
symbol XST7f [H] [x : String] [y : String] [P Q : Prd] [R]
  : ⁇ (pnf x R and pnf y P and pnf y R)
  → ⁇ (prd_eq (psub x (eid y) P) Q)
  → ▷ (H ⟝ ∀ y (Q ⇒ R))
  → ▷ (H ⟝ (∃ x P) ⇒ R);

// Spec: "x not free in H".
// TODO: "x nf H" not checked.
symbol XST8 [H x P]
  : Π R : Res (H ⟝ ¬ P),
    ▷ (H ⟝ (∀ x (obtain R)) ⇒ FALSE)
  → ▷ (H ⟝ ∃ x P);

// Spec: "x free in H; y free in
// neither A nor H; P = [x:=y]A".
// TODO: "y nf H" not checked.
symbol XST8f [H] [x : String] [y : String] [A P : Prd]
  : ⁇ (pnf y A)
  → ⁇ (prd_eq (psub x (eid y) A) P)
  → Π R : Res (H ⟝ ¬ P),
    ▷ (H ⟝ (∀ x (obtain R)) ⇒ FALSE)
  → ▷ (H ⟝ ∃ x A);

// ---- Primed variants ----

// XST8′: like ALL7′ for existential quantification.
symbol XST8_1 [H x P]
  : Π R : Res (H ⟝ ¬ P),
    Res (H ⟝ (∀ x (obtain R)) ⇒ FALSE)
  → Res (H ⟝ ∃ x P);
rule obtain (XST8_1 _ $r) ↪ obtain $r;

// XST8f′: like ALL7f′ for existential quantification.
symbol XST8f_1 [H] [x : String] [y : String] [A P : Prd]
  : ⁇ (pnf y A)
  → ⁇ (prd_eq (psub x (eid y) A) P)
  → Π R : Res (H ⟝ ¬ P),
    Res (H ⟝ (∀ x (obtain R)) ⇒ FALSE)
  → Res (H ⟝ ∃ x A);
rule obtain (XST8f_1 _ _ _ $r) ↪ obtain $r;

symbol XST1_1 [H] [x y : Var] [P R]
  : ⁇ (vneq x y)
  → Res (H ⟝ ¬ (∃ (x ⨾ y) P) ⇒ R)
  → Res (H ⟝ ¬ (∃ x (∃ y P)) ⇒ R);
rule obtain (XST1_1 _ $r) ↪ obtain $r;

symbol XST2_1 [H] [x y : Var] [P]
  : ⁇ (vneq x y)
  → Res (H ⟝ ¬ (∃ (x ⨾ y) P))
  → Res (H ⟝ ¬ (∃ x (∃ y P)));
rule obtain (XST2_1 _ $r) ↪ obtain $r;

symbol XST3_1 [H] [x y : Var] [P R]
  : ⁇ (vneq x y)
  → Res (H ⟝ (∃ (x ⨾ y) P) ⇒ R)
  → Res (H ⟝ (∃ x (∃ y P)) ⇒ R);
rule obtain (XST3_1 _ $r) ↪ obtain $r;

symbol XST4_1 [H] [x y : Var] [P]
  : ⁇ (vneq x y)
  → Res (H ⟝ ∃ (x ⨾ y) P)
  → Res (H ⟝ ∃ x (∃ y P));
rule obtain (XST4_1 _ $r) ↪ obtain $r;

symbol XST5_1 [H x P R]
  : Res (H ⟝ (∀ x (¬ P)) ⇒ R)
  → Res (H ⟝ ¬ (∃ x P) ⇒ R);
rule obtain (XST5_1 $r) ↪ obtain $r;

symbol XST51_1 [H x P R]
  : Res (H ⟝ (∀ x P) ⇒ R)
  → Res (H ⟝ ¬ (∃ x (¬ P)) ⇒ R);
rule obtain (XST51_1 $r) ↪ obtain $r;

symbol XST6_1 [H x P]
  : Res (H ⟝ ∀ x (¬ P))
  → Res (H ⟝ ¬ (∃ x P));
rule obtain (XST6_1 $r) ↪ obtain $r;

symbol XST61_1 [H x P]
  : Res (H ⟝ ∀ x P)
  → Res (H ⟝ ¬ (∃ x (¬ P)));
rule obtain (XST61_1 $r) ↪ obtain $r;

symbol XST7_1 [H x P R]
  : ⁇ (vpnf x R)
  → Res (H ⟝ ∀ x (P ⇒ R))
  → Res (H ⟝ (∃ x P) ⇒ R);
rule obtain (XST7_1 _ $r) ↪ obtain $r;

symbol XST7f_1 [H] [x : String] [y : String] [P Q : Prd] [R]
  : ⁇ (pnf y P and pnf y R)
  → ⁇ (prd_eq (psub x (eid y) P) Q)
  → Res (H ⟝ ∀ y (Q ⇒ R))
  → Res (H ⟝ (∃ x P) ⇒ R);
rule obtain (XST7f_1 _ _ $r) ↪ obtain $r;
