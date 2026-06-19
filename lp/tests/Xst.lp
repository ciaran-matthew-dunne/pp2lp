// Tests for rules/Xst.lp (existential quantifier, tuple-indexed).
require open pp2lp.Prelude;

// XST1–4: compound ↔ nested conversions.
symbol t_XST1 (n : ℕ) (P : Tuple n → Tuple 1 → Prop) (R : Prop)
  (h : π (¬ (`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)) ⇒ R))
  : π (¬ (`?? w : Tuple n, `?? y : Tuple 1, P w y) ⇒ R) ≔ XST1 h;
symbol t_XST2 (n : ℕ) (P : Tuple n → Tuple 1 → Prop)
  (h : π (¬ (`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v))))
  : π (¬ (`?? w : Tuple n, `?? y : Tuple 1, P w y)) ≔ XST2 h;
symbol t_XST3 (n : ℕ) (P : Tuple n → Tuple 1 → Prop) (R : Prop)
  (h : π ((`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)) ⇒ R))
  : π ((`?? w : Tuple n, `?? y : Tuple 1, P w y) ⇒ R) ≔ XST3 h;
symbol t_XST4 (n : ℕ) (P : Tuple n → Tuple 1 → Prop)
  (h : π (`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)))
  : π (`?? w : Tuple n, `?? y : Tuple 1, P w y) ≔ XST4 h;

// XST5–8 (and 51/61): ∃ ↔ ∀ De Morgan and ∃-introduction.
symbol t_XST5 (n : ℕ) (P : Tuple n → Prop) (R : Prop)
  (h : π ((`!! v, ¬ (P v)) ⇒ R)) : π (¬ (`?? v, P v) ⇒ R) ≔ XST5 h;
symbol t_XST51 (n : ℕ) (P : Tuple n → Prop) (R : Prop)
  (h : π ((`!! v, P v) ⇒ R)) : π (¬ (`?? v, ¬ (P v)) ⇒ R) ≔ XST51 h;
symbol t_XST6 (n : ℕ) (P : Tuple n → Prop)
  (h : π (`!! v, ¬ (P v))) : π (¬ (`?? v, P v)) ≔ XST6 h;
symbol t_XST61 (n : ℕ) (P : Tuple n → Prop)
  (h : π (`!! v, P v)) : π (¬ (`?? v, ¬ (P v))) ≔ XST61 h;
symbol t_XST7 (n : ℕ) (P : Tuple n → Prop) (R : Prop)
  (h : π (`!! v, P v ⇒ R)) : π ((`?? v, P v) ⇒ R) ≔ XST7 h;
symbol t_XST8 (n : ℕ) (P : Tuple n → Prop)
  (ρ : Π v : Tuple n, Res (¬ (P v))) (h : π ((`!! v, res_tm (ρ v)) ⇒ ⊥))
  : π (`?? v, P v) ≔ XST8 ρ h;

// _1 (Result-form) variants
// Curried binder-merge chain forms (XST1_1–XST4_1).
symbol t_XST1_1 (n : ℕ) (P : Tuple n → Tuple 1 → Prop) (R : Prop)
  (r : Res (¬ (`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)) ⇒ R))
  : Res (¬ (`?? w : Tuple n, `?? y : Tuple 1, P w y) ⇒ R) ≔ XST1_1 r;
symbol t_XST2_1 (n : ℕ) (P : Tuple n → Tuple 1 → Prop)
  (r : Res (¬ (`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v))))
  : Res (¬ (`?? w : Tuple n, `?? y : Tuple 1, P w y)) ≔ XST2_1 r;
symbol t_XST3_1 (n : ℕ) (P : Tuple n → Tuple 1 → Prop) (R : Prop)
  (r : Res ((`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)) ⇒ R))
  : Res ((`?? w : Tuple n, `?? y : Tuple 1, P w y) ⇒ R) ≔ XST3_1 r;
symbol t_XST4_1 (n : ℕ) (P : Tuple n → Tuple 1 → Prop)
  (r : Res (`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)))
  : Res (`?? w : Tuple n, `?? y : Tuple 1, P w y) ≔ XST4_1 r;
symbol t_XST5_1 (n : ℕ) (P : Tuple n → Prop) (R : Prop)
  (r : Res ((`!! v, ¬ (P v)) ⇒ R)) : Res (¬ (`?? v, P v) ⇒ R) ≔ XST5_1 r;
symbol t_XST51_1 (n : ℕ) (P : Tuple n → Prop) (R : Prop)
  (r : Res ((`!! v, P v) ⇒ R)) : Res (¬ (`?? v, ¬ (P v)) ⇒ R) ≔ XST51_1 r;
symbol t_XST6_1 (n : ℕ) (P : Tuple n → Prop)
  (r : Res (`!! v, ¬ (P v))) : Res (¬ (`?? v, P v)) ≔ XST6_1 r;
symbol t_XST61_1 (n : ℕ) (P : Tuple n → Prop)
  (r : Res (`!! v, P v)) : Res (¬ (`?? v, ¬ (P v))) ≔ XST61_1 r;
symbol t_XST7_1 (n : ℕ) (P : Tuple n → Prop) (R : Prop)
  (r : Res (`!! v, P v ⇒ R)) : Res ((`?? v, P v) ⇒ R) ≔ XST7_1 r;
symbol t_XST8_1 (n : ℕ) (P : Tuple n → Prop)
  (ρ : Π v : Tuple n, Res (¬ (P v))) (r : Res ((`!! v, res_tm (ρ v)) ⇒ ⊥))
  : Res (`?? v, P v) ≔ XST8_1 ρ r;
