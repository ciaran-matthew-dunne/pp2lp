// Normalisation (§A.12)
require open
  pp2lp.B pp2lp.Eq
  pp2lp.NonFree pp2lp.Subst
  pp2lp.Proof;

// ---- Base rules ----

symbol NRM1 [H x P S]
  : ⁇ (vpnf x P)
  → ▷ (H ⟝ P ⇒ S)
  → ▷ (H ⟝ (♢ x P) ⇒ S);

symbol NRM2 [H] [x : Var] [P Q S]
  : ⁇ (vpnf x P)
  → ▷ (H ⟝ (P ⇒ ♢ x Q) ⇒ S)
  → ▷ (H ⟝ (♢ x (P ⇒ Q)) ⇒ S);

// Spec also requires "Q is not FALSE"
// (dispatch condition, not checked).
symbol NRM3 [H] [x : Var] [P Q S]
  : ⁇ (vpnf x Q)
  → ⁇ (not (prd_eq Q FALSE))
  → ▷ (H ⟝ (Q ⇒ S) ∧ ((∀ x (¬ P)) ⇒ S))
  → ▷ (H ⟝ (♢ x (P ⇒ Q)) ⇒ S);

symbol NRM4 [H] [x : Var] [P Q R S]
  : ⁇ (vpnf x Q)
  → ▷ (H ⟝ (Q ⇒ ♢ x (P ⇒ R)) ⇒ S)
  → ▷ (H ⟝ (♢ x (P ⇒ (Q ⇒ R))) ⇒ S);

symbol NRM5 [H x P Q R S]
  : ▷ (H ⟝ (♢ x (P ∧ Q ⇒ R)) ⇒ S)
  → ▷ (H ⟝ (♢ x (P ⇒ (Q ⇒ R))) ⇒ S);

symbol NRM6 [H x P Q R S]
  : ▷ (H ⟝ (♢ x (R ⇒ P)) ⇒ ((♢ x (R ⇒ Q)) ⇒ S))
  → ▷ (H ⟝ (♢ x (R ⇒ P ∧ Q)) ⇒ S);

symbol NRM7 [H x P Q S]
  : ▷ (H ⟝ (♢ x P) ⇒ ((♢ x Q) ⇒ S))
  → ▷ (H ⟝ (♢ x (P ∧ Q)) ⇒ S);

symbol NRM8 [H] [x y] [Q S]
  : ⁇ (vneq x y)
  → ▷ (H ⟝ (♢ (x ⨾ y) Q) ⇒ S)
  → ▷ (H ⟝ (♢ x (∀ y Q)) ⇒ S);

symbol NRM8f [H] [x : Var] [y z : String] [Q K S : Prd]
  : ⁇ (veq x y)
  → ⁇ ((vneq x z) and (vneq z y))
  → ⁇ (prd_eq (psub y (eid z) Q) K)
  → ▷ (H ⟝ (♢ (x ⨾ z) K) ⇒ S)
  → ▷ (H ⟝ (♢ x (∀ y Q)) ⇒ S);

// Spec: "x and y distinct;
// y not free in P".
symbol NRM9 [H] [x y : Var] [P Q S]
  : ⁇ (vneq x y)
  → ⁇ (vpnf y P)
  → ▷ (H ⟝ (♢ (x ⨾ y) (P ⇒ Q)) ⇒ S)
  → ▷ (H ⟝ (♢ x (P ⇒ ∀ y Q)) ⇒ S);

symbol NRM9f [H] [x y z : String] [P] [Q K : Prd] [S]
  : ⁇ ((veq x y) or (not (vpnf y P)))
  → ⁇ ((vneq z x) and (vpnf z P) and (vpnf z Q))
  → ⁇ (prd_eq (psub y (eid z) Q) K)
  → ▷ (H ⟝ (♢ (x ⨾ z) (P ⇒ K)) ⇒ S)
  → ▷ (H ⟝ (♢ x (P ⇒ ∀ y Q)) ⇒ S);

symbol NRM10 [H x P Q R]
  : ▷ (H ⟝ (♡ x (¬ (P ∧ Q))) ⇒ R)
  → ▷ (H ⟝ (♢ x ((P ∧ Q) ⇒ FALSE)) ⇒ R);

symbol NRM11 [H x P R]
  : ▷ (H ⟝ (♡ x (¬ (TRUE ∧ P))) ⇒ R)
  → ▷ (H ⟝ (♢ x (P ⇒ FALSE)) ⇒ R);

symbol NRM12 [H x P Q R]
  : ▷ (H ⟝ (♡ x (¬ (P ∧ Q))) ⇒ R)
  → ▷ (H ⟝ (♢ x (P ⇒ ¬ Q)) ⇒ R);

symbol NRM13 [H x P Q R]
  : ▷ (H ⟝ (♡ x (¬ (P ∧ ¬ Q))) ⇒ R)
  → ▷ (H ⟝ (♢ x (P ⇒ Q)) ⇒ R);

symbol NRM14 [H x P R]
  : ▷ (H ⟝ (♡ x (¬ (TRUE ∧ P))) ⇒ R)
  → ▷ (H ⟝ (♢ x (¬ P)) ⇒ R);

symbol NRM15 [H x P R]
  : ▷ (H ⟝ (♡ x (¬ (TRUE ∧ ¬ P))) ⇒ R)
  → ▷ (H ⟝ (♢ x P) ⇒ R);

symbol NRM16 [H x P Q]
  : ⁇ ((∀ x P) dans H)
  → ▷ (H ⟝ (♡ x P) ⇒ Q);

// Spec: "∃E. [x:=E]P = R" (substitution matching).
symbol NRM17 [H] [x : Var] [y] (E : Exp) [P R Q]
  : ⁇ (∀ x (¬ (TRUE ∧ P)) dans H)
  → ⁇ (prd_eq (vpsub x E P) R)
  → ▷ (H ⟝ (♡ y (¬ (TRUE ∧ ¬ R))) ⇒ Q);

// Spec: "∃E. [x:=E]P = R" (substitution matching).
symbol NRM18 [H] [x : Var] [y] (E : Exp) [P R Q]
  : ⁇ (∀ x (¬ (TRUE ∧ ¬ P)) dans H)
  → ⁇ (prd_eq (vpsub x E P) R)
  → ▷ (H ⟝ (♡ y (¬ (TRUE ∧ R))) ⇒ Q);

// Spec requires "∃E. [x:=E]R = P"
// Uses vpsub to handle compound Var.
symbol NRM19 [H] [x : Var] (P : Prd) (E : Exp) [R Q]
  : ⁇ (P dans H)
  → ⁇ (prd_eq (vpsub x E R) P)
  → ▷ (H ⟝ (♡ x (¬ (TRUE ∧ R))) ⇒ Q);

symbol NRM20 [H] [x : String] [y : Var] [E P Q]
  : ⁇ (enf x E)
  → ▷ (H ⟝ (♡ y (¬ (psub x E P))) ⇒ Q)
  → ▷ (H ⟝ (♡ (x ⨾ y) (¬ (P ∧ (eid x ≃ E)))) ⇒ Q);

symbol NRM21 [H] [x : String] [y : Var] [E P Q]
  : ⁇ (enf x E)
  → ▷ (H ⟝ (♡ y (¬ (psub x E P))) ⇒ Q)
  → ▷ (H ⟝ (♡ (x ⨾ y) (¬ (P ∧ (E ≃ eid x)))) ⇒ Q);

symbol NRM22 [H] [x : String] [E P Q]
  : ⁇ (enf x E)
  → ▷ (H ⟝ ¬ (psub x E P) ⇒ Q)
  → ▷ (H ⟝ (♡ x (¬ (P ∧ (eid x ≃ E)))) ⇒ Q);

symbol NRM23 [H] [x : String] [E P Q]
  : ⁇ (enf x E)
  → ▷ (H ⟝ ¬ (psub x E P) ⇒ Q)
  → ▷ (H ⟝ (♡ x (¬ (P ∧ (E ≃ eid x)))) ⇒ Q);

// Spec: "P is not of the form A∧B"
sequential symbol ?conj : Prd → 𝔹;
rule ?conj ($p ∧ $p') ↪ true
with ?conj _ ↪ false;


symbol NRM24 [H x P Q]
  : ⁇ (not (?conj P))
  → ▷ (H ⟝ (♡ x (¬ (TRUE ∧ P))) ⇒ Q)
  → ▷ (H ⟝ (♡ x (¬ P)) ⇒ Q);

symbol NRM25 [H] [x : Var] [P]
  : ⁇ (vpnf x P)
  → ▷ (H ⟝ P)
  → ▷ (H ⟝ ♡ x P);

symbol NRM26 [H] [x y : Var] [P]
  : ⁇ (vpnf y P)
  → ▷ (H ⟝ ♡ x P)
  → ▷ (H ⟝ ♡ (x ⨾ y) P);

// Spec: (xᵢ ≤ 0) and (−xᵢ ≤ 0) in conjunction;
// R = [xᵢ := 0](P ∧ ... ∧ Q).
// Conjunction membership is a dispatch condition, not checked.
symbol NRM27 [H] [xs xs' : Var] [xi : String] [P R : Prd]
  : ⁇ (prd_eq (psub xi 𝟎 P) R)
  → ▷ (H ⟝ ♢ xs' (¬ R))
  → ▷ (H ⟝ ♡ xs (¬ P));

// Spec: (x ≤ 0) and (−x ≤ 0) in conjunction;
// S = [x := 0](P ∧ ... ∧ Q).
// Conjunction membership is a dispatch condition, not checked.
symbol NRM28 [H] [x : String] [P S R : Prd]
  : ⁇ (prd_eq (psub x 𝟎 P) S)
  → ▷ (H ⟝ ¬ S ⇒ R)
  → ▷ (H ⟝ (♡ x (¬ P)) ⇒ R);

// Spec: (a + xᵢ ≤ 0) and (b − xᵢ ≤ 0) in conjunction;
// solver(a + b) = 0; S = [xᵢ := b](P ∧ ... ∧ Q).
// Conjunction membership and solver check are dispatch conditions.
// Also covers spec's NRM29_1 (xᵢ + a, −xᵢ + b coefficient pattern).
symbol NRM29 [H] [xs xs' : Var] [xi : String]
             (b : Exp) [P S R : Prd]
  : ⁇ (prd_eq (psub xi b P) S)
  → ▷ (H ⟝ (♢ xs' (¬ S)) ⇒ R)
  → ▷ (H ⟝ (♡ xs (¬ P)) ⇒ R);

// Spec: (a + x ≤ 0) and (b − x ≤ 0) in conjunction;
// solver(a + b) = 0; S = [x := b](P ∧ ... ∧ Q).
// Conjunction membership and solver check are dispatch conditions.
// Also covers spec's NRM30_1 (x + a, −x + b coefficient pattern).
symbol NRM30 [H] [x : String] (b : Exp) [P S R : Prd]
  : ⁇ (prd_eq (psub x b P) S)
  → ▷ (H ⟝ ¬ S ⇒ R)
  → ▷ (H ⟝ (♡ x (¬ P)) ⇒ R);

// ---- Primed variants (Schema 0) ----

symbol NRM16_1 [H x P Q]
  : ⁇ (∀ x P dans H)
  → Res (H ⟝ (♡ x P) ⇒ Q);
rule obtain (NRM16_1 _) ↪ TRUE;

symbol NRM17_1 [H] [x : Var] [y] (E : Exp) [P R Q]
  : ⁇ (∀ x (¬ (TRUE ∧ P)) dans H)
  → ⁇ (prd_eq (vpsub x E P) R)
  → Res (H ⟝ (♡ y (¬ (TRUE ∧ ¬ R))) ⇒ Q);
rule obtain (NRM17_1 _ _ _) ↪ TRUE;

symbol NRM18_1 [H] [x : Var] [y] (E : Exp) [P R Q]
  : ⁇ (∀ x (¬ (TRUE ∧ ¬ P)) dans H)
  → ⁇ (prd_eq (vpsub x E P) R)
  → Res (H ⟝ (♡ y (¬ (TRUE ∧ R))) ⇒ Q);
rule obtain (NRM18_1 _ _ _) ↪ TRUE;

symbol NRM19_1 [H] [x : Var] (P : Prd) [R Q]
  : ⁇ (P dans H)
  → Res (H ⟝ (♡ x (¬ (TRUE ∧ R))) ⇒ Q);
rule obtain (NRM19_1 _ _) ↪ TRUE;

// ---- Primed variants (Schema 1) ----

symbol NRM1_1 [H x P S]
  : ⁇ (vpnf x P)
  → Res (H ⟝ P ⇒ S)
  → Res (H ⟝ (♢ x P) ⇒ S);
rule obtain (NRM1_1 _ $r) ↪ obtain $r;

symbol NRM2_1 [H] [x : Var] [P Q S]
  : ⁇ (vpnf x P)
  → Res (H ⟝ (P ⇒ ♢ x Q) ⇒ S)
  → Res (H ⟝ (♢ x (P ⇒ Q)) ⇒ S);
rule obtain (NRM2_1 _ $r) ↪ obtain $r;

symbol NRM3_1 [H] [x : Var] [P Q S]
  : ⁇ (vpnf x Q)
  → Res (H ⟝ (Q ⇒ S) ∧ ((∀ x (¬ P)) ⇒ S))
  → Res (H ⟝ (♢ x (P ⇒ Q)) ⇒ S);
rule obtain (NRM3_1 _ $r) ↪ obtain $r;

symbol NRM4_1 [H] [x : Var] [P Q R S]
  : ⁇ (vpnf x Q)
  → Res (H ⟝ (Q ⇒ ♢ x (P ⇒ R)) ⇒ S)
  → Res (H ⟝ (♢ x (P ⇒ (Q ⇒ R))) ⇒ S);
rule obtain (NRM4_1 _ $r) ↪ obtain $r;

symbol NRM5_1 [H x P Q R S]
  : Res (H ⟝ (♢ x (P ∧ Q ⇒ R)) ⇒ S)
  → Res (H ⟝ (♢ x (P ⇒ (Q ⇒ R))) ⇒ S);
rule obtain (NRM5_1 $r) ↪ obtain $r;

symbol NRM6_1 [H x P Q R S]
  : Res (H ⟝ (♢ x (R ⇒ P)) ⇒ ((♢ x (R ⇒ Q)) ⇒ S))
  → Res (H ⟝ (♢ x (R ⇒ P ∧ Q)) ⇒ S);
rule obtain (NRM6_1 $r) ↪ obtain $r;

symbol NRM7_1 [H x P Q S]
  : Res (H ⟝ (♢ x P) ⇒ ((♢ x Q) ⇒ S))
  → Res (H ⟝ (♢ x (P ∧ Q)) ⇒ S);
rule obtain (NRM7_1 $r) ↪ obtain $r;

symbol NRM8_1 [H] [x y : Var] [Q S]
  : ⁇ (vneq x y)
  → Res (H ⟝ (♢ (x ⨾ y) Q) ⇒ S)
  → Res (H ⟝ (♢ x (∀ y Q)) ⇒ S);
rule obtain (NRM8_1 _ $r) ↪ obtain $r;

symbol NRM8f_1 [H] [x : Var] [y z : String] [Q K : Prd] [S]
  : ⁇ (veq x y)
  → ⁇ ((vneq x z) and (vneq z y))
  → ⁇ (prd_eq (psub y (eid z) Q) K)
  → Res (H ⟝ (♢ (x ⨾ z) K) ⇒ S)
  → Res (H ⟝ (♢ x (∀ y Q)) ⇒ S);
rule obtain (NRM8f_1 _ _ _ $r) ↪ obtain $r;

symbol NRM8c_1 [H] [x y z : Var] [Q S]
  : ⁇ (vneq (x ⨾ y) z)
  → Res (H ⟝ (♢ (x ⨾ (y ⨾ z)) Q) ⇒ S)
  → Res (H ⟝ (♢ (x ⨾ y) (∀ z Q)) ⇒ S);
rule obtain (NRM8c_1 _ $r) ↪ obtain $r;

symbol NRM9_1 [H] [x y : Var] [P Q S]
  : ⁇ (vneq x y)
  → ⁇ (vpnf y P)
  → Res (H ⟝ (♢ (x ⨾ y) (P ⇒ Q)) ⇒ S)
  → Res (H ⟝ (♢ x (P ⇒ ∀ y Q)) ⇒ S);
rule obtain (NRM9_1 _ _ $r) ↪ obtain $r;

symbol NRM9f_1 [H] [x : Var] [y z : String] [P] [Q K : Prd] [S]
  : ⁇ ((veq x y) or (not (vpnf y P)))
  → ⁇ ((vneq z x) and (vpnf z P) and (vpnf z Q))
  → ⁇ (prd_eq (psub y (eid z) Q) K)
  → Res (H ⟝ (♢ (x ⨾ z) (P ⇒ K)) ⇒ S)
  → Res (H ⟝ (♢ x (P ⇒ ∀ y Q)) ⇒ S);
rule obtain (NRM9f_1 _ _ _ $r) ↪ obtain $r;

symbol NRM10_1 [H x P Q R]
  : Res (H ⟝ (♡ x (¬ (P ∧ Q))) ⇒ R)
  → Res (H ⟝ (♢ x ((P ∧ Q) ⇒ FALSE)) ⇒ R);
rule obtain (NRM10_1 $r) ↪ obtain $r;

symbol NRM11_1 [H x P R]
  : Res (H ⟝ (♡ x (¬ (TRUE ∧ P))) ⇒ R)
  → Res (H ⟝ (♢ x (P ⇒ FALSE)) ⇒ R);
rule obtain (NRM11_1 $r) ↪ obtain $r;

symbol NRM12_1 [H x P Q R]
  : Res (H ⟝ (♡ x (¬ (P ∧ Q))) ⇒ R)
  → Res (H ⟝ (♢ x (P ⇒ ¬ Q)) ⇒ R);
rule obtain (NRM12_1 $r) ↪ obtain $r;

symbol NRM13_1 [H x P Q R]
  : Res (H ⟝ (♡ x (¬ (P ∧ ¬ Q))) ⇒ R)
  → Res (H ⟝ (♢ x (P ⇒ Q)) ⇒ R);
rule obtain (NRM13_1 $r) ↪ obtain $r;

symbol NRM14_1 [H x P R]
  : Res (H ⟝ (♡ x (¬ (TRUE ∧ P))) ⇒ R)
  → Res (H ⟝ (♢ x (¬ P)) ⇒ R);
rule obtain (NRM14_1 $r) ↪ obtain $r;

symbol NRM15_1 [H x P R]
  : Res (H ⟝ (♡ x (¬ (TRUE ∧ ¬ P))) ⇒ R)
  → Res (H ⟝ (♢ x P) ⇒ R);
rule obtain (NRM15_1 $r) ↪ obtain $r;

symbol NRM20_1 [H] [x : String] [y : Var] [E P Q]
  : ⁇ (enf x E)
  → Res (H ⟝ (♡ y (¬ (psub x E P))) ⇒ Q)
  → Res (H ⟝ (♡ (x ⨾ y) (¬ (P ∧ (eid x ≃ E)))) ⇒ Q);
rule obtain (NRM20_1 _ $r) ↪ obtain $r;

symbol NRM21_1 [H] [x : String] [y : Var] [E P Q]
  : ⁇ (enf x E)
  → Res (H ⟝ (♡ y (¬ (psub x E P))) ⇒ Q)
  → Res (H ⟝ (♡ (x ⨾ y) (¬ (P ∧ (E ≃ eid x)))) ⇒ Q);
rule obtain (NRM21_1 _ $r) ↪ obtain $r;

symbol NRM22_1 [H] [x : String] [E P Q]
  : ⁇ (enf x E)
  → Res (H ⟝ ¬ (psub x E P) ⇒ Q)
  → Res (H ⟝ (♡ x (¬ (P ∧ (eid x ≃ E)))) ⇒ Q);
rule obtain (NRM22_1 _ $r) ↪ obtain $r;

symbol NRM23_1 [H] [x : String] [E P Q]
  : ⁇ (enf x E)
  → Res (H ⟝ ¬ (psub x E P) ⇒ Q)
  → Res (H ⟝ (♡ x (¬ (P ∧ (E ≃ eid x)))) ⇒ Q);
rule obtain (NRM23_1 _ $r) ↪ obtain $r;

symbol NRM24_1 [H x P Q]
  : ⁇ (not (?conj P))
  → Res (H ⟝ (♡ x (¬ (TRUE ∧ P))) ⇒ Q)
  → Res (H ⟝ (♡ x (¬ P)) ⇒ Q);
rule obtain (NRM24_1 _ $r) ↪ obtain $r;

symbol NRM25_1 [H] [x : Var] [P]
  : ⁇ (vpnf x P)
  → Res (H ⟝ P)
  → Res (H ⟝ ♡ x P);
rule obtain (NRM25_1 _ $r) ↪ obtain $r;

symbol NRM26_1 [H] [x y : Var] [P]
  : ⁇ (vpnf y P)
  → Res (H ⟝ ♡ x P)
  → Res (H ⟝ ♡ (x ⨾ y) P);
rule obtain (NRM26_1 _ $r) ↪ obtain $r;

symbol NRM27_1 [H] [xs xs' : Var] [xi : String] [P R : Prd]
  : ⁇ (prd_eq (psub xi 𝟎 P) R)
  → Res (H ⟝ ♢ xs' (¬ R))
  → Res (H ⟝ ♡ xs (¬ P));
rule obtain (NRM27_1 _ $r) ↪ obtain $r;

symbol NRM28_1 [H] [x : String] [P S R : Prd]
  : ⁇ (prd_eq (psub x 𝟎 P) S)
  → Res (H ⟝ ¬ S ⇒ R)
  → Res (H ⟝ (♡ x (¬ P)) ⇒ R);
rule obtain (NRM28_1 _ $r) ↪ obtain $r;

symbol NRM29_1 [H] [xs xs' : Var] [xi : String]
               (b : Exp) [P S R : Prd]
  : ⁇ (prd_eq (psub xi b P) S)
  → Res (H ⟝ (♢ xs' (¬ S)) ⇒ R)
  → Res (H ⟝ (♡ xs (¬ P)) ⇒ R);
rule obtain (NRM29_1 _ _ $r) ↪ obtain $r;

symbol NRM30_1 [H] [x : String] (b : Exp) [P S R : Prd]
  : ⁇ (prd_eq (psub x b P) S)
  → Res (H ⟝ ¬ S ⇒ R)
  → Res (H ⟝ (♡ x (¬ P)) ⇒ R);
rule obtain (NRM30_1 _ _ $r) ↪ obtain $r;
