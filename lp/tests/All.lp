// Tests for rules/All.lp (universal quantifier, tuple-indexed).
// Quantifier arity is left abstract (n : ℕ) so each test exercises the
// uniform tuple-indexed form, not a fixed arity.
require open pp2lp.Prelude;

// ALL1–4: compound ↔ nested conversions.
symbol t_ALL1 (n : ℕ) (P : Tuple n → Tuple 1 → Prop) (R : Prop)
  (h : π (¬ (`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)) ⇒ R))
  : π (¬ (`!! w : Tuple n, `!! y : Tuple 1, P w y) ⇒ R) ≔ ALL1 h;
symbol t_ALL2 (n : ℕ) (P : Tuple n → Tuple 1 → Prop)
  (h : π (¬ (`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v))))
  : π (¬ (`!! w : Tuple n, `!! y : Tuple 1, P w y)) ≔ ALL2 h;
symbol t_ALL3 (n : ℕ) (P : Tuple n → Tuple 1 → Prop) (R : Prop)
  (h : π ((`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)) ⇒ R))
  : π ((`!! w : Tuple n, `!! y : Tuple 1, P w y) ⇒ R) ≔ ALL3 h;
symbol t_ALL4 (n : ℕ) (P : Tuple n → Tuple 1 → Prop)
  (h : π (`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)))
  : π (`!! w : Tuple n, `!! y : Tuple 1, P w y) ≔ ALL4 h;

// ALL5–9.
symbol t_ALL5 (n : ℕ) (P : Tuple n → Prop) (R : Prop)
  (h : π (`!! v, ¬ (P v) ⇒ R)) : π (¬ (`!! v, P v) ⇒ R) ≔ ALL5 h;
symbol t_ALL6 (n : ℕ) (P : Tuple n → Prop)
  (h : π ((`!! v, P v) ⇒ ⊥)) : π (¬ (`!! v, P v)) ≔ ALL6 h;
symbol t_ALL7 (n : ℕ) (P : Tuple n → Prop) (Q : Prop)
  (ρ : Π v : Tuple n, Res (P v)) (h : π ((`♢ v, res_tm (ρ v)) ⇒ Q))
  : π ((`!! v, P v) ⇒ Q) ≔ ALL7 ρ h;
symbol t_ALL8 (n : ℕ) (P : Tuple n → Prop) (f : Π v : Tuple n, π (P v))
  : π (`!! v, P v) ≔ ALL8 f;
symbol t_ALL9 (n : ℕ) (T : Tuple n → Prop) (Q : Prop)
  (h : π (`!! v, T v) → π Q) : π ((`♡ v, T v) ⇒ Q) ≔ ALL9 h;

// _1 (Result-form) variants
// Curried binder-merge chain forms (ALL1_1–ALL4_1).
symbol t_ALL1_1 (n : ℕ) (P : Tuple n → Tuple 1 → Prop) (R : Prop)
  (r : Res (¬ (`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)) ⇒ R))
  : Res (¬ (`!! w : Tuple n, `!! y : Tuple 1, P w y) ⇒ R) ≔ ALL1_1 r;
symbol t_ALL2_1 (n : ℕ) (P : Tuple n → Tuple 1 → Prop)
  (r : Res (¬ (`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v))))
  : Res (¬ (`!! w : Tuple n, `!! y : Tuple 1, P w y)) ≔ ALL2_1 r;
symbol t_ALL3_1 (n : ℕ) (P : Tuple n → Tuple 1 → Prop) (R : Prop)
  (r : Res ((`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)) ⇒ R))
  : Res ((`!! w : Tuple n, `!! y : Tuple 1, P w y) ⇒ R) ≔ ALL3_1 r;
symbol t_ALL4_1 (n : ℕ) (P : Tuple n → Tuple 1 → Prop)
  (r : Res (`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)))
  : Res (`!! w : Tuple n, `!! y : Tuple 1, P w y) ≔ ALL4_1 r;
symbol t_ALL6_1 (n : ℕ) (P : Tuple n → Prop)
  (r : Res ((`!! v, P v) ⇒ ⊥)) : Res (¬ (`!! v, P v)) ≔ ALL6_1 r;
symbol t_ALL7_1 (n : ℕ) (P : Tuple n → Prop) (Q : Prop)
  (ρ : Π v : Tuple n, Res (P v)) (r : Res ((`♢ v, res_tm (ρ v)) ⇒ Q))
  : Res ((`!! v, P v) ⇒ Q) ≔ ALL7_1 ρ r;
symbol t_ALL8_1 (n : ℕ) (P : Tuple n → Prop) (ρ : Π v : Tuple n, Res (P v))
  : Res (`!! v, P v) ≔ ALL8_1 ρ;
symbol t_ALL9_1 (n : ℕ) (T : Tuple n → Prop) (Q : Prop) (r : Res Q)
  : Res ((`♡ v, T v) ⇒ Q) ≔ @ALL9_1 n T Q r;
