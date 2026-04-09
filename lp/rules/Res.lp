// Res P: proof-with-result for normalisation chains.
// result is computed from constructors via rewrite rules.
// All constructor args are implicit — inferred by lambdapi from context.
require open pp2lp.B pp2lp.rules.Rw;

constant symbol Res : Prop → TYPE;
injective symbol result [P : Prop] : Res P → Prop;
symbol to_eq [P : Prop] (r : Res P) : π (P = result r);

// ---- STOP ----
constant symbol stop_r [P : Prop] : Res P;
rule result (@stop_r $P) ↪ $P;

// ---- Schema 1: passthrough ----

constant symbol and2_r [P Q : Prop] : Res (P ⇒ ¬ Q) → Res (¬ (P ∧ Q));
rule result (and2_r $h) ↪ result $h;

constant symbol and3_r [P Q R : Prop] : Res (P ⇒ Q ⇒ R) → Res ((P ∧ Q) ⇒ R);
rule result (and3_r $h) ↪ result $h;

constant symbol or4_r [P Q : Prop] : Res (¬ P ⇒ Q) → Res (P ∨ Q);
rule result (or4_r $h) ↪ result $h;

constant symbol vr3_r [P : Prop] : Res P → Res (⊤ ⇒ P);
rule result (vr3_r $h) ↪ result $h;

constant symbol evr2_r [E : τ ι] : Res ⊥ → Res (¬ (E = E));
rule result (evr2_r $h) ↪ result $h;

constant symbol not1_r [P R : Prop] : Res (P ⇒ R) → Res (¬ ¬ P ⇒ R);
rule result (not1_r $h) ↪ result $h;

constant symbol xst7_r [P : τ ι → Prop] [R : Prop]
  : Res (`∀ x, P x ⇒ R) → Res ((`∃ x, P x) ⇒ R);
rule result (xst7_r $h) ↪ result $h;

constant symbol evr3_r [E : τ ι] [P : Prop] : Res P → Res ((E = E) ⇒ P);
rule result (evr3_r $h) ↪ result $h;

constant symbol or1_r [P Q R : Prop]
  : Res (¬ P ⇒ ¬ Q ⇒ R) → Res (¬ (P ∨ Q) ⇒ R);
rule result (or1_r $h) ↪ result $h;

constant symbol imp1_r [P Q R : Prop]
  : Res (P ⇒ ¬ Q ⇒ R) → Res (¬ (P ⇒ Q) ⇒ R);
rule result (imp1_r $h) ↪ result $h;

constant symbol imp5_r [P Q : Prop] : Res Q → Res (P ⇒ Q);
rule result (imp5_r $h) ↪ result $h;

constant symbol not2_r [P : Prop] : Res P → Res (¬ ¬ P);
rule result (not2_r $h) ↪ result $h;

constant symbol vr2_r : Res ⊥ → Res (¬ ⊤);
rule result (vr2_r $h) ↪ result $h;

constant symbol fx1_r [P : Prop] : Res P → Res (¬ ⊥ ⇒ P);
rule result (fx1_r $h) ↪ result $h;

// EQV: schema 2 (branching)
constant symbol eqv1_r [P Q R : Prop]
  : Res (P ⇒ ¬ Q ⇒ R) → Res (¬ P ⇒ Q ⇒ R) → Res (¬ (P ⇔ Q) ⇒ R);
rule result (eqv1_r $h1 $h2) ↪ result $h1 ∧ result $h2;

constant symbol eqv2_r [P Q : Prop]
  : Res (¬ Q) → Res P → Res (¬ (P ⇔ Q));
rule result (eqv2_r $h1 $h2) ↪ result $h1 ∧ result $h2;

constant symbol eqv3_r [P Q R : Prop]
  : Res (Q ⇒ R) → Res (P ⇒ R) → Res ((P ⇔ Q) ⇒ R);
rule result (eqv3_r $h1 $h2) ↪ result $h1 ∧ result $h2;

constant symbol eqv4_r [P Q : Prop]
  : Res (Q ⇒ P) → Res (P ⇒ Q) → Res (P ⇔ Q);
rule result (eqv4_r $h1 $h2) ↪ result $h1 ∧ result $h2;

// OPR1/OPR2: substitution under equality
// PE (child consequent) is explicit; Px (goal consequent) inferred from context.
constant symbol opr1_r [x E : τ ι] (PE : Prop) [Px : Prop]
  : Res ((x = E) ⇒ PE) → Res ((x = E) ⇒ Px);
rule result (opr1_r _ $h) ↪ result $h;

constant symbol opr2_r [E x : τ ι] (PE : Prop) [Px : Prop]
  : Res ((E = x) ⇒ PE) → Res ((E = x) ⇒ Px);
rule result (opr2_r _ $h) ↪ result $h;

// AR9: solver equality E=F
constant symbol ar9_r [E F : τ ι] [R : Prop]
  : π (E = F) → Res ((F ≤ 𝟎) ⇒ R) → Res ((E ≤ 𝟎) ⇒ R);
rule result (ar9_r _ $h) ↪ result $h;

// ---- Schema 2: branching (result = S1 ∧ S2) ----

constant symbol and1_r [P Q R : Prop]
  : Res (¬ Q ⇒ R) → Res (¬ P ⇒ R) → Res (¬ (P ∧ Q) ⇒ R);
rule result (and1_r $h1 $h2) ↪ result $h1 ∧ result $h2;

constant symbol or3_r [P Q R : Prop]
  : Res (Q ⇒ R) → Res (P ⇒ R) → Res ((P ∨ Q) ⇒ R);
rule result (or3_r $h1 $h2) ↪ result $h1 ∧ result $h2;

constant symbol and4_r [P Q : Prop]
  : Res Q → Res P → Res (P ∧ Q);
rule result (and4_r $h1 $h2) ↪ result $h1 ∧ result $h2;

constant symbol imp3_r [P Q R : Prop]
  : Res (Q ⇒ R) → Res (¬ P ⇒ R) → Res ((P ⇒ Q) ⇒ R);
rule result (imp3_r $h1 $h2) ↪ result $h1 ∧ result $h2;

constant symbol or2_r [P Q : Prop]
  : Res (¬ Q) → Res (¬ P) → Res (¬ (P ∨ Q));
rule result (or2_r $h1 $h2) ↪ result $h1 ∧ result $h2;

constant symbol imp2_r [P Q : Prop]
  : Res (¬ Q) → Res P → Res (¬ (P ⇒ Q));
rule result (imp2_r $h1 $h2) ↪ result $h1 ∧ result $h2;

// ---- Structural ----

constant symbol imp4_r [P Q : Prop] : Res Q → Res (P ⇒ Q);
rule result (@imp4_r $P _ $h) ↪ $P ⇒ result $h;

constant symbol all8_r [P : τ ι → Prop]
  : (Π x : τ ι, Res (P x)) → Res (`∀ x, P x);
rule result (all8_r $f) ↪ `∀ x, result ($f x);

constant symbol all9_r [H Q : Prop] : Res Q → Res (H ⇒ Q);
rule result (@all9_r $H _ $h) ↪ $H ⇒ result $h;

constant symbol and5_r [C C' R : Prop]
  : (π C → π C') → (π C' → π C) → Res (C' ⇒ R) → Res (C ⇒ R);
rule result (and5_r _ _ $h) ↪ result $h;

// ---- ALL7 with dependent type ----

symbol ALL7r [P : τ ι → Prop] [Q : Prop]
  (h1 : Π x : τ ι, Res (P x))
  (h2 : π ((`♢ x, result (h1 x)) ⇒ Q))
  : π ((`∀ x, P x) ⇒ Q) ≔
  λ hP, h2 (λ x, =⇒ (to_eq (h1 x)) (hP x));

symbol ALL7_2r [P : τ ι → τ ι → Prop] [Q : Prop]
  (h1 : Π x : τ ι, Π y : τ ι, Res (P x y))
  (h2 : π ((`♢ x, `♢ y, result (h1 x y)) ⇒ Q))
  : π ((`∀ x, `∀ y, P x y) ⇒ Q) ≔
  λ hP, h2 (λ x y, =⇒ (to_eq (h1 x y)) (hP x y));

// ---- XST8 with Res: existential via ¬¬ elimination ----
// XST8: (H ⊢ ¬P) ⇝ R; H ⊢ (∀x·R) ⇒ ⊥ → H ⊢ ∃x·P
// The result chain computes R from ¬P. We need ¬(P x) = result(h1 x),
// then the continuation proves (∀x, result(h1 x)) ⇒ ⊥.

symbol XST8r [P : τ ι → Prop]
  (h1 : Π x : τ ι, Res (¬ (P x)))
  (h2 : π ((`∀ x, result (h1 x)) ⇒ ⊥))
  : π (`∃ x, P x) ≔
  ¬¬ₑ _ (λ hne, h2 (λ x, =⇒ (to_eq (h1 x)) (λ hpx, hne (∃ᵢ x hpx))));

symbol XST8_2r [P : τ ι → τ ι → Prop]
  (h1 : Π x : τ ι, Π y : τ ι, Res (¬ (P x y)))
  (h2 : π ((`∀ x, `∀ y, result (h1 x y)) ⇒ ⊥))
  : π (`∃ x, `∃ y, P x y) ≔
  ¬¬ₑ _ (λ hne, h2 (λ x y, =⇒ (to_eq (h1 x y)) (λ hpxy, hne (∃ᵢ x (∃ᵢ y hpxy)))));
