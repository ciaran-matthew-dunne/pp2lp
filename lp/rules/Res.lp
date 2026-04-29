// Res.lp — _res rules: Σ-type encoding of normalisation chains.
// `Res t = (t' : τ a) × π (t = t')` packages a normalised term with a
// proof of equality to the original. Each `_res` rule is a Res-to-Res
// wrapper around the corresponding `_1` rule in Rw.lp; chains are now
// term-level function compositions (e.g. `AND2_res (VR3_res STOP_res)`)
// where `res_tm` projects the final normal form and `res_eq` projects
// the cumulative equality witness.
require open pp2lp.B pp2lp.rules.Rw pp2lp.rules.All;

// ---- Res infrastructure ----

injective symbol Res [a : Set] : τ a → TYPE;
symbol mk_res [a t] (t' : τ a) : π (t = t') → Res t;
sequential symbol res_tm [a t] : Res [a] t → τ a;
sequential symbol res_eq [a t] (r : Res [a] t) : π (t = res_tm r);
rule res_tm (mk_res $t' _) ↪ $t';
rule res_eq (mk_res _ $prf) ↪ $prf;

// ---- Leaf ----

symbol STOP_res [P : Prop] : Res P
  ≔ mk_res P (eq_refl P);

// ---- Structural _res rules ----

symbol IMP4_res [P Q : Prop] (r : Res Q) : Res (P ⇒ Q)
  ≔ mk_res (P ⇒ res_tm r) (IMP4_1 (res_eq r));

symbol IMP5_res [P Q : Prop] (hp : π P) (r : Res Q) : Res (P ⇒ Q)
  ≔ mk_res (res_tm r) (IMP5_1 hp (res_eq r));

symbol ALL8_res [P : τ ι → Prop] (ρ : Π x, Res (P x)) : Res (`∀ x, P x)
  ≔ mk_res (`∀ x, res_tm (ρ x)) (ALL8_1 (λ x, res_eq (ρ x)));

symbol NRM1_res [P Q : Prop] (r : Res (P ⇒ Q))
  : Res ((`♢ _ : τ ι, P) ⇒ Q)
  ≔ mk_res (res_tm r) (NRM1_1 (res_eq r));

symbol ALL7_res [P : τ ι → Prop] [Q : Prop]
  (ρ : Π x, Res (P x))
  (r : Res ((`♢ x, res_tm (ρ x)) ⇒ Q))
  : Res ((`∀ x, P x) ⇒ Q)
  ≔ mk_res (res_tm r)
      (ALL7_1 (λ x, res_tm (ρ x)) (λ x, res_eq (ρ x)) (res_eq r));

symbol ALL7_res_2 [P : τ ι → τ ι → Prop] [Q : Prop]
  (ρ : Π x y, Res (P x y))
  (r : Res ((`♢ x, `♢ y, res_tm (ρ x y)) ⇒ Q))
  : Res ((`∀ x, `∀ y, P x y) ⇒ Q)
  ≔ mk_res (res_tm r)
      (ALL7_1_2 (λ x y, res_tm (ρ x y))
                (λ x y, res_eq (ρ x y))
                (res_eq r));

symbol ALL7_res_3 [P : τ ι → τ ι → τ ι → Prop] [Q : Prop]
  (ρ : Π x y z, Res (P x y z))
  (r : Res ((`♢ x, `♢ y, `♢ z, res_tm (ρ x y z)) ⇒ Q))
  : Res ((`∀ x, `∀ y, `∀ z, P x y z) ⇒ Q)
  ≔ mk_res (res_tm r)
      (ALL7_1_3 (λ x y z, res_tm (ρ x y z))
                (λ x y z, res_eq (ρ x y z))
                (res_eq r));

symbol XST7_res [P : τ ι → Prop] [R : Prop]
  (r : Res (`∀ x, P x ⇒ R)) : Res ((`∃ x, P x) ⇒ R)
  ≔ mk_res (res_tm r) (XST7_1 (res_eq r));

symbol XST8_res [P : τ ι → Prop]
  (r : Res ((`∀ x, ¬ (P x)) ⇒ ⊥)) : Res (`∃ x, P x)
  ≔ mk_res (res_tm r) (XST8_1 (res_eq r));

symbol XST8_res_2 [P : τ ι → τ ι → Prop]
  (r : Res ((`∀ x, `∀ y, ¬ (P x y)) ⇒ ⊥))
  : Res (`∃ x, `∃ y, P x y)
  ≔ mk_res (res_tm r) (XST8_1_2 (res_eq r));

symbol XST8_res_3 [P : τ ι → τ ι → τ ι → Prop]
  (r : Res ((`∀ x, `∀ y, `∀ z, ¬ (P x y z)) ⇒ ⊥))
  : Res (`∃ x, `∃ y, `∃ z, P x y z)
  ≔ mk_res (res_tm r) (XST8_1_3 (res_eq r));

symbol ALL9_res [H Q : Prop] (r : Res Q) : Res (H ⇒ Q)
  ≔ mk_res (H ⇒ res_tm r) (ALL9_1 (res_eq r));

// ---- Passthrough _res rules ----

symbol AND2_res [P Q : Prop] (r : Res (P ⇒ ¬ Q)) : Res (¬ (P ∧ Q))
  ≔ mk_res (res_tm r) (AND2_1 (res_eq r));

symbol AND3_res [P Q R : Prop] (r : Res (P ⇒ Q ⇒ R))
  : Res ((P ∧ Q) ⇒ R)
  ≔ mk_res (res_tm r) (AND3_1 (res_eq r));

symbol OR1_res [P Q R : Prop] (r : Res (¬ P ⇒ ¬ Q ⇒ R))
  : Res (¬ (P ∨ Q) ⇒ R)
  ≔ mk_res (res_tm r) (OR1_1 (res_eq r));

symbol OR4_res [P Q : Prop] (r : Res (¬ P ⇒ Q)) : Res (P ∨ Q)
  ≔ mk_res (res_tm r) (OR4_1 (res_eq r));

symbol NOT1_res [P R : Prop] (r : Res (P ⇒ R)) : Res (¬ ¬ P ⇒ R)
  ≔ mk_res (res_tm r) (NOT1_1 (res_eq r));

symbol OPR1_res [E : τ ι] (P : τ ι → Prop) (x : τ ι)
  (r : Res (x = E ⇒ P E)) : Res (x = E ⇒ P x)
  ≔ mk_res (res_tm r) (OPR1_1 P x (res_eq r));

symbol OPR2_res [E : τ ι] (P : τ ι → Prop) (x : τ ι)
  (r : Res (E = x ⇒ P E)) : Res (E = x ⇒ P x)
  ≔ mk_res (res_tm r) (OPR2_1 P x (res_eq r));

symbol NOT2_res [P : Prop] (r : Res P) : Res (¬ ¬ P)
  ≔ mk_res (res_tm r) (NOT2_1 (res_eq r));

symbol IMP1_res [P Q R : Prop] (r : Res (P ⇒ ¬ Q ⇒ R))
  : Res (¬ (P ⇒ Q) ⇒ R)
  ≔ mk_res (res_tm r) (IMP1_1 (res_eq r));

symbol VR3_res [P : Prop] (r : Res P) : Res (⊤ ⇒ P)
  ≔ mk_res (res_tm r) (VR3_1 (res_eq r));

symbol EVR2_res [E : τ ι] (r : Res ⊥) : Res (¬ (E = E))
  ≔ mk_res (res_tm r) (EVR2_1 (res_eq r));

symbol EVR3_res [E : τ ι] [P : Prop] (r : Res P)
  : Res ((E = E) ⇒ P)
  ≔ mk_res (res_tm r) (EVR3_1 (res_eq r));

// ---- left_∧: left-fold combinator for AND4 chains ----
// `left_∧ x y` left-folds x into the binary ∧-tree y, accumulating on the
// left. This fires automatically and correctly at any chain depth:
//   left_∧ r (q ∧ p)       ↪ left_∧ (r ∧ q) p ↪ (r ∧ q) ∧ p
//   left_∧ d ((c ∧ b) ∧ a) ↪ left_∧ (left_∧ d (c ∧ b)) a ↪ ((d ∧ c) ∧ b) ∧ a
// The recursive rule dismantles the right side completely, so no post-hoc
// `rewrite ∧_assoc` is needed at the call site.
sequential symbol left_∧ : τ o → τ o → τ o;
rule left_∧ $x ($a ∧ $b) ↪ left_∧ (left_∧ $x $a) $b
with left_∧ $x $y ↪ $x ∧ $y;

//sequential symbol left_∧_eq (x y : τ o) : π ((x ∧ y) = left_∧ x y);
//rule left_∧_eq $x ($a ∧ $b) ↪
//  eq_trans ∧_assoc
//    (eq_trans (conj_eq (left_∧_eq $x $a) (eq_refl $b))
//              (left_∧_eq (left_∧ $x $a) $b))
//with left_∧_eq $x $y ↪ eq_refl ($x ∧ $y);

// ---- Branching _res rules ----

symbol AND1_res [P Q R : Prop]
  (r1 : Res (¬ Q ⇒ R)) (r2 : Res (¬ P ⇒ R))
  : Res (¬ (P ∧ Q) ⇒ R)
  ≔ mk_res (res_tm r1 ∧ res_tm r2)
      (AND1_1 (res_eq r1) (res_eq r2));

symbol AND4_res [P Q : Prop] (r1 : Res Q) (r2 : Res P) : Res (P ∧ Q)
  ≔ mk_res (left_∧ (res_tm r1) (res_tm r2))
           (AND4_1 (res_eq r1) (res_eq r2));

symbol OR2_res [P Q : Prop]
  (r1 : Res (¬ Q)) (r2 : Res (¬ P)) : Res (¬ (P ∨ Q))
  ≔ mk_res (res_tm r1 ∧ res_tm r2)
      (OR2_1 (res_eq r1) (res_eq r2));

symbol OR3_res [P Q R : Prop]
  (r1 : Res (Q ⇒ R)) (r2 : Res (P ⇒ R))
  : Res ((P ∨ Q) ⇒ R)
  ≔ mk_res (res_tm r1 ∧ res_tm r2)
      (OR3_1 (res_eq r1) (res_eq r2));

symbol IMP3_res [P Q R : Prop]
  (r1 : Res (Q ⇒ R)) (r2 : Res (¬ P ⇒ R))
  : Res ((P ⇒ Q) ⇒ R)
  ≔ mk_res (res_tm r1 ∧ res_tm r2)
      (IMP3_1 (res_eq r1) (res_eq r2));

symbol IMP2_res [P Q : Prop]
  (r1 : Res (¬ Q)) (r2 : Res P) : Res (¬ (P ⇒ Q))
  ≔ mk_res (res_tm r1 ∧ res_tm r2)
      (IMP2_1 (res_eq r1) (res_eq r2));

symbol EQV1_res [P Q R : Prop]
  (r1 : Res (P ⇒ ¬ Q ⇒ R)) (r2 : Res (¬ P ⇒ Q ⇒ R))
  : Res (¬ (P ⇔ Q) ⇒ R)
  ≔ mk_res (res_tm r1 ∧ res_tm r2)
      (EQV1_1 (res_eq r1) (res_eq r2));

symbol EQV3_res [P Q R : Prop]
  (r1 : Res (P ⇒ Q ⇒ R)) (r2 : Res (¬ P ⇒ ¬ Q ⇒ R))
  : Res ((P ⇔ Q) ⇒ R)
  ≔ mk_res (res_tm r1 ∧ res_tm r2)
      (EQV3_1 (res_eq r1) (res_eq r2));

// ---- Chain-exit (π-valued) ----
// Closes a per-x Res chain into the propositional form expected by the
// outer `ALL7` rule. Useful when ALL7 is at the top of a goal: the inner
// chain runs through `_res` rules, then `ALL7_close` discharges to π.
opaque symbol ALL7_close [P : τ ι → Prop] [Q : Prop]
  (ρ : Π x, Res (P x))
  : π ((`♢ x, res_tm (ρ x)) ⇒ Q) → π ((`∀ x, P x) ⇒ Q)
  ≔ λ h, ALL7 (λ x, res_tm (ρ x)) (λ x, res_eq (ρ x)) h;

opaque symbol ALL7_close_2 [P : τ ι → τ ι → Prop] [Q : Prop]
  (ρ : Π x y, Res (P x y))
  : π ((`♢ x, `♢ y, res_tm (ρ x y)) ⇒ Q)
  → π ((`∀ x, `∀ y, P x y) ⇒ Q)
  ≔ λ h, ALL7_2 (λ x y, res_tm (ρ x y))
                (λ x y, res_eq (ρ x y)) h;

opaque symbol ALL7_close_3 [P : τ ι → τ ι → τ ι → Prop] [Q : Prop]
  (ρ : Π x y z, Res (P x y z))
  : π ((`♢ x, `♢ y, `♢ z, res_tm (ρ x y z)) ⇒ Q)
  → π ((`∀ x, `∀ y, `∀ z, P x y z) ⇒ Q)
  ≔ λ h, ALL7_3 (λ x y z, res_tm (ρ x y z))
                (λ x y z, res_eq (ρ x y z)) h;
