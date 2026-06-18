// Tests for rules/Eq.lp (equality: EVR / EAXM / EIMP / OPR / EQC / EQS / ECTR).
require open pp2lp.Prelude;

// ---- EVR (reflexivity) ----
symbol t_EVR1 (E : τ ι) (P : Prop) : π (¬ (E = E) ⇒ P) ≔ @EVR1 E P;
symbol t_EVR11 (n m : τ ι) (P : Prop)
  (h1 : π (n ϵ NAT)) (h2 : π (m ϵ NAT)) (h3 : π (n ≠ m)) : π ((n = m) ⇒ P) ≔ EVR11 h1 h2 h3;
symbol t_EVR2 (E : τ ι) (h : π ⊥) : π (¬ (E = E)) ≔ EVR2 h;
symbol t_EVR3 (E : τ ι) (P : Prop) (h : π P) : π ((E = E) ⇒ P) ≔ EVR3 h;
symbol t_EVR4 (E : τ ι) : π (E = E) ≔ @EVR4 E;

// ---- EAXM (commutativity) ----
symbol t_EAXM1 (E F : τ ι) (P : Prop) (h : π (¬ (F = E))) : π ((E = F) ⇒ P) ≔ EAXM1 h;
symbol t_EAXM2 (E F : τ ι) (P : Prop) (h : π (F = E)) : π (¬ (E = F) ⇒ P) ≔ EAXM2 h;
symbol t_EAXM31 (E F : τ ι) (h : π (F = E)) : π (E = F) ≔ EAXM31 h;
symbol t_EAXM32 (E F : τ ι) (h : π (¬ (F = E))) : π (¬ (E = F)) ≔ EAXM32 h;

// ---- EIMP ----
symbol t_EIMP51 (E F : τ ι) (P : Prop) (h1 : π (¬ (F = E))) (h2 : π P)
  : π (¬ (E = F) ⇒ P) ≔ EIMP51 h1 h2;
symbol t_EIMP52 (E F : τ ι) (P : Prop) (h1 : π (F = E)) (h2 : π P)
  : π ((E = F) ⇒ P) ≔ EIMP52 h1 h2;

// ---- EAXM91/92 (AXM9 extensions for eq commutativity) ----
symbol t_EAXM91 (n : ℕ) (p q : Tuple n → τ ι) (v : Tuple n) (Q : Prop)
  (h : π (`!! u, ¬ (⊤ ∧ (p u = q u)))) : π ((q v = p v) ⇒ Q) ≔ EAXM91 v h;
symbol t_EAXM92 (n : ℕ) (p q : Tuple n → τ ι) (v : Tuple n) (Q : Prop)
  (h : π (`!! u, ¬ (⊤ ∧ ¬ (p u = q u)))) : π (¬ (q v = p v) ⇒ Q) ≔ EAXM92 v h;

// ---- OPR (one-point) ----
symbol t_OPR1 (E x : τ ι) (P : τ ι → Prop) (h : π (P E)) : π ((x = E) ⇒ P x) ≔ OPR1 P h;
symbol t_OPR2 (E x : τ ι) (P : τ ι → Prop) (h : π (P E)) : π ((E = x) ⇒ P x) ≔ OPR2 P h;

// ---- EQC (pair equality decomposition) ----
symbol t_EQC1 (a b c d : τ ι) (P : Prop) (h : π ((¬ (a = c) ∨ ¬ (b = d)) ⇒ P))
  : π (¬ ((a ↦ b) = (c ↦ d)) ⇒ P) ≔ EQC1 h;
symbol t_EQC2 (a b c d : τ ι) (P : Prop) (h : π (⋀ (∎ ∷ (a = c) ∷ (b = d)) ⇒ P))
  : π (((a ↦ b) = (c ↦ d)) ⇒ P) ≔ EQC2 h;

// ---- EQS (set equality) ----
symbol t_EQS1 (E F : τ ι) (R : Prop) (h : π ((E = F) ⇒ R)) : π (eql_set E F ⇒ R) ≔ EQS1 h;
symbol t_EQS2 (E F : τ ι) (R : Prop) (h1 : π (eql_set E F)) (h2 : π (⊥ ⇒ R))
  : π (¬ eql_set E F ⇒ R) ≔ EQS2 h1 h2;

// ---- ECTR (contradiction via substitution) ----
symbol t_ECTR1 (E F : τ ι) (Q : τ ι → Prop) (P : Prop) (h1 : π (¬ (Q E))) (h2 : π (Q F))
  : π ((E = F) ⇒ P) ≔ ECTR1 Q h1 h2;
symbol t_ECTR2 (E F : τ ι) (Q : τ ι → Prop) (P : Prop) (h1 : π (¬ (Q E))) (h2 : π (Q F))
  : π ((F = E) ⇒ P) ≔ ECTR2 Q h1 h2;
symbol t_ECTR3 (E F : τ ι) (P : τ ι → Prop) (Q : Prop) (h1 : π (E = F)) (h2 : π (P F))
  : π (¬ (P E) ⇒ Q) ≔ ECTR3 P h1 h2;
symbol t_ECTR4 (E F : τ ι) (P : τ ι → Prop) (Q : Prop) (h1 : π (F = E)) (h2 : π (P F))
  : π (¬ (P E) ⇒ Q) ≔ ECTR4 P h1 h2;
symbol t_ECTR5 (E F : τ ι) (P : τ ι → Prop) (Q : Prop) (h1 : π (E = F)) (h2 : π (¬ (P F)))
  : π ((P E) ⇒ Q) ≔ ECTR5 P h1 h2;
symbol t_ECTR6 (E F : τ ι) (P : τ ι → Prop) (Q : Prop) (h1 : π (F = E)) (h2 : π (¬ (P F)))
  : π ((P E) ⇒ Q) ≔ ECTR6 P h1 h2;

// ---- _1 (Result-form) variants ----
symbol t_EVR1_1 (E : τ ι) (P : Prop) : Res (¬ (E = E) ⇒ P) ≔ @EVR1_1 E P;
symbol t_EVR2_1 (E : τ ι) (r : Res ⊥) : Res (¬ (E = E)) ≔ EVR2_1 r;
symbol t_EVR3_1 (E : τ ι) (P : Prop) (r : Res P) : Res ((E = E) ⇒ P) ≔ @EVR3_1 E P r;
symbol t_EVR4_1 (E : τ ι) : Res (E = E) ≔ @EVR4_1 E;
symbol t_EVR11_1 (n m : τ ι) (P : Prop) (h : π (¬ (n = m))) : Res ((n = m) ⇒ P) ≔ EVR11_1 h;
symbol t_EAXM1_1 (E F : τ ι) (P : Prop) (h : π (¬ (F = E))) : Res ((E = F) ⇒ P) ≔ EAXM1_1 h;
symbol t_EAXM2_1 (E F : τ ι) (P : Prop) (h : π (F = E)) : Res (¬ (E = F) ⇒ P) ≔ EAXM2_1 h;
symbol t_EAXM31_1 (E F : τ ι) (r : Res (F = E)) : Res (E = F) ≔ EAXM31_1 r;
symbol t_EAXM32_1 (E F : τ ι) (r : Res (¬ (F = E))) : Res (¬ (E = F)) ≔ EAXM32_1 r;
symbol t_EIMP51_1 (E F : τ ι) (P : Prop) (h : π (¬ (E = F))) (r : Res P)
  : Res (¬ (E = F) ⇒ P) ≔ EIMP51_1 h r;
symbol t_EIMP52_1 (E F : τ ι) (P : Prop) (h : π (E = F)) (r : Res P)
  : Res ((E = F) ⇒ P) ≔ EIMP52_1 h r;
// p, q passed explicitly: `q v = p v` over a free v is not a Miller pattern,
// so the implicit predicates can't be recovered by unification.
symbol t_EAXM91_1 (n : ℕ) (p q : Tuple n → τ ι) (v : Tuple n) (Q : Prop)
  (h : π (q v = p v)) (r : Res Q) : Res ((q v = p v) ⇒ Q) ≔ @EAXM91_1 n p q v Q h r;
symbol t_EAXM92_1 (n : ℕ) (p q : Tuple n → τ ι) (v : Tuple n) (Q : Prop)
  (h : π (¬ (q v = p v))) (r : Res Q) : Res (¬ (q v = p v) ⇒ Q) ≔ @EAXM92_1 n p q v Q h r;
symbol t_OPR1_1 (E x : τ ι) (P : τ ι → Prop) (r : Res (x = E ⇒ P E))
  : Res (x = E ⇒ P x) ≔ OPR1_1 P r;
symbol t_OPR2_1 (E x : τ ι) (P : τ ι → Prop) (r : Res (E = x ⇒ P E))
  : Res (E = x ⇒ P x) ≔ OPR2_1 P r;
symbol t_EQC1_1 (a b c d : τ ι) (P : Prop) (r : Res ((¬ (a = c) ∨ ¬ (b = d)) ⇒ P))
  : Res (¬ ((a ↦ b) = (c ↦ d)) ⇒ P) ≔ EQC1_1 r;
symbol t_EQC2_1 (a b c d : τ ι) (P : Prop) (r : Res (⋀ (∎ ∷ (a = c) ∷ (b = d)) ⇒ P))
  : Res (((a ↦ b) = (c ↦ d)) ⇒ P) ≔ EQC2_1 r;
symbol t_EQS1_1 (E F : τ ι) (R : Prop) (r : Res ((E = F) ⇒ R)) : Res (eql_set E F ⇒ R) ≔ EQS1_1 r;
symbol t_EQS2_1 (E F : τ ι) (R : Prop) (r : Res (¬ (E = F) ⇒ R))
  : Res (¬ eql_set E F ⇒ R) ≔ EQS2_1 r;
symbol t_ECTR1_1 (E F : τ ι) (Q : τ ι → Prop) (P : Prop) (h1 : π (¬ (Q E))) (h2 : π (Q F))
  : Res ((E = F) ⇒ P) ≔ ECTR1_1 Q h1 h2;
symbol t_ECTR2_1 (E F : τ ι) (Q : τ ι → Prop) (P : Prop) (h1 : π (¬ (Q E))) (h2 : π (Q F))
  : Res ((F = E) ⇒ P) ≔ ECTR2_1 Q h1 h2;
symbol t_ECTR3_1 (E F : τ ι) (P : τ ι → Prop) (Q : Prop) (h1 : π (E = F)) (h2 : π (P F))
  : Res (¬ (P E) ⇒ Q) ≔ ECTR3_1 P h1 h2;
symbol t_ECTR4_1 (E F : τ ι) (P : τ ι → Prop) (Q : Prop) (h1 : π (F = E)) (h2 : π (P F))
  : Res (¬ (P E) ⇒ Q) ≔ ECTR4_1 P h1 h2;
symbol t_ECTR5_1 (E F : τ ι) (P : τ ι → Prop) (Q : Prop) (h1 : π (E = F)) (h2 : π (¬ (P F)))
  : Res ((P E) ⇒ Q) ≔ ECTR5_1 P h1 h2;
symbol t_ECTR6_1 (E F : τ ι) (P : τ ι → Prop) (Q : Prop) (h1 : π (F = E)) (h2 : π (¬ (P F)))
  : Res ((P E) ⇒ Q) ≔ ECTR6_1 P h1 h2;
