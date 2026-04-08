// Universal quantification (§A.7)
require open
  pp2lp.B pp2lp.Eq
  pp2lp.NonFree pp2lp.Subst
  pp2lp.Proof;

// ---- Base rules ----

// Spec: "x and y are distinct".
symbol ALL1 [H] [x y : Var] [P R]
  : ⁇ (vneq x y)
  → ▷ (H ⟝ ¬ (∀ (x ⨾ y) P) ⇒ R)
  → ▷ (H ⟝ ¬ (∀ x (∀ y P)) ⇒ R);

symbol ALL2 [H] [x y : Var] [P]
  : ⁇ (vneq x y)
  → ▷ (H ⟝ ¬ (∀ (x ⨾ y) P))
  → ▷ (H ⟝ ¬ (∀ x (∀ y P)));

symbol ALL3 [H] [x y : Var] [P R]
  : ⁇ (vneq x y)
  → ▷ (H ⟝ (∀ (x ⨾ y) P) ⇒ R)
  → ▷ (H ⟝ (∀ x (∀ y P)) ⇒ R);

symbol ALL4 [H] [x y : Var] [P]
  : ⁇ (vneq x y)
  → ▷ (H ⟝ ∀ (x ⨾ y) P)
  → ▷ (H ⟝ ∀ x (∀ y P));

// Spec: "x not free in R".
symbol ALL5 [H x P R]
  : ⁇ (vpnf x R)
  → ▷ (H ⟝ ∀ x (¬ P ⇒ R))
  → ▷ (H ⟝ ¬ (∀ x P) ⇒ R);

// Spec: "x free in R; y free in
// neither P nor R; S = [x:=y]P".
symbol ALL5f [H] [x : String] [y : String] [P S : Prd] [R]
  : ⁇ (pnf y P and pnf y R)
  → ⁇ (prd_eq (psub x (eid y) P) S)
  → ▷ (H ⟝ ∀ y (¬ S ⇒ R))
  → ▷ (H ⟝ ¬ (∀ x P) ⇒ R);

symbol ALL6 [H x P]
  : ▷ (H ⟝ (∀ x P) ⇒ FALSE)
  → ▷ (H ⟝ ¬ (∀ x P));

// Spec: "x not free in H".
// TODO: "x nf H" not checked
// (H is Hyp, not Prd).
symbol ALL7 [H x P Q]
  : Π R : Res (H ⟝ P),
    ▷ (H ⟝ (♢ x (obtain R)) ⇒ Q)
  → ▷ (H ⟝ (∀ x P) ⇒ Q);

// Spec: "x free in H; y free in
// neither A nor H; P = [x:=y]A".
// TODO: "y nf H" not checked.
symbol ALL7f [H] [x : String] [y : String] [A P : Prd] [Q]
  : ⁇ (pnf y A)
  → ⁇ (prd_eq (psub x (eid y) A) P)
  → Π R : Res (H ⟝ P),
    ▷ (H ⟝ (♢ x (obtain R)) ⇒ Q)
  → ▷ (H ⟝ (∀ x A) ⇒ Q);

// Spec: "x not free in H".
// TODO: "x nf H" not checked.
symbol ALL8 [H x P]
  : ▷ (H ⟝ P)
  → ▷ (H ⟝ ∀ x P);

// Spec: "x free in H; y free in
// neither P nor H; R = [x:=y]P".
// TODO: "y nf H" not checked.
symbol ALL8f [H] [x : String] [y : String] [P R : Prd]
  : ⁇ (pnf y P)
  → ⁇ (prd_eq (psub x (eid y) P) R)
  → ▷ (H ⟝ R)
  → ▷ (H ⟝ ∀ x P);

symbol ALL9 [H x T Q]
  : ▷ (((∀ x T) ∷ H) ⟝ Q)
  → ▷ (H ⟝ (♡ x T) ⇒ Q);

// ---- Primed variants ----

// ALL7′: result passes through from the second subgoal.
symbol ALL7_1 [H x P Q]
  : Π R : Res (H ⟝ P),
    Res (H ⟝ (♢ x (obtain R)) ⇒ Q)
  → Res (H ⟝ (∀ x P) ⇒ Q);
rule obtain (ALL7_1 _ $r) ↪ obtain $r;

// ALL7f′: like ALL7′ with free-variable renaming.
symbol ALL7f_1 [H] [x : String] [y : String] [A P : Prd] [Q]
  : ⁇ (pnf y A)
  → ⁇ (prd_eq (psub x (eid y) A) P)
  → Π R : Res (H ⟝ P),
    Res (H ⟝ (♢ x (obtain R)) ⇒ Q)
  → Res (H ⟝ (∀ x A) ⇒ Q);
rule obtain (ALL7f_1 _ _ _ $r) ↪ obtain $r;

// ALL8′: result = ∀x · R (quantifier wraps body result).
symbol ALL8_1 [H] [x : Var] [P]
  : Res (H ⟝ P)
  → Res (H ⟝ ∀ x P);
rule obtain (ALL8_1 [_] [$x] [_] $r) ↪ ∀ $x (obtain $r);

// ALL8f′: result = ∀y · R (renamed quantifier wraps body result).
symbol ALL8f_1 [H] [x : String] [y : String] [P R : Prd]
  : ⁇ (pnf y P)
  → ⁇ (prd_eq (psub x (eid y) P) R)
  → Res (H ⟝ R)
  → Res (H ⟝ ∀ x P);
rule obtain (ALL8f_1 [_] [_] [$y] [_] [_] _ _ $r) ↪ ∀ (id $y) (obtain $r);

// ALL9′: result = (∀x · T) ⇒ R.
symbol ALL9_1 [H] [x : Var] [T : Prd] [Q]
  : Res (((∀ x T) ∷ H) ⟝ Q)
  → Res (H ⟝ (♡ x T) ⇒ Q);
rule obtain (ALL9_1 [_] [$x] [$T] [_] $r) ↪ (∀ $x $T) ⇒ obtain $r;

symbol ALL1_1 [H] [x y : Var] [P R]
  : ⁇ (vneq x y)
  → Res (H ⟝ ¬ (∀ (x ⨾ y) P) ⇒ R)
  → Res (H ⟝ ¬ (∀ x (∀ y P)) ⇒ R);
rule obtain (ALL1_1 _ $r) ↪ obtain $r;

symbol ALL2_1 [H] [x y : Var] [P]
  : ⁇ (vneq x y)
  → Res (H ⟝ ¬ (∀ (x ⨾ y) P))
  → Res (H ⟝ ¬ (∀ x (∀ y P)));
rule obtain (ALL2_1 _ $r) ↪ obtain $r;

symbol ALL3_1 [H] [x y : Var] [P R]
  : ⁇ (vneq x y)
  → Res (H ⟝ (∀ (x ⨾ y) P) ⇒ R)
  → Res (H ⟝ (∀ x (∀ y P)) ⇒ R);
rule obtain (ALL3_1 _ $r) ↪ obtain $r;

symbol ALL4_1 [H] [x y : Var] [P]
  : ⁇ (vneq x y)
  → Res (H ⟝ ∀ (x ⨾ y) P)
  → Res (H ⟝ ∀ x (∀ y P));
rule obtain (ALL4_1 _ $r) ↪ obtain $r;

symbol ALL5_1 [H x P R]
  : ⁇ (vpnf x R)
  → Res (H ⟝ ∀ x (¬ P ⇒ R))
  → Res (H ⟝ ¬ (∀ x P) ⇒ R);
rule obtain (ALL5_1 _ $r) ↪ obtain $r;

symbol ALL5f_1 [H] [x : String] [y : String] [P S : Prd] [R]
  : ⁇ (pnf y P and pnf y R)
  → ⁇ (prd_eq (psub x (eid y) P) S)
  → Res (H ⟝ ∀ y (¬ S ⇒ R))
  → Res (H ⟝ ¬ (∀ x P) ⇒ R);
rule obtain (ALL5f_1 _ _ $r) ↪ obtain $r;

symbol ALL6_1 [H x P]
  : Res (H ⟝ (∀ x P) ⇒ FALSE)
  → Res (H ⟝ ¬ (∀ x P));
rule obtain (ALL6_1 $r) ↪ obtain $r;
