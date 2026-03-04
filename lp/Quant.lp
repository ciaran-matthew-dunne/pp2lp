// Quantification rules (spec §A.7 + §A.8)
require open pp2lp.B pp2lp.Eq pp2lp.Interp;

// ==== Universal quantification (§A.7) ====

// ALL1–ALL4: grouping of nested quantifications.
symbol ALL1 [H x y P R]
  : ⁇ (nf y (#prd (∀ x (∀ y P))))
  → (H ⊩ ¬ (∀ (x ⨾ y) P) ⇒ R) → (H ⊩ ¬ (∀ x (∀ y P)) ⇒ R);

symbol ALL2 [H x y P]
  : ⁇ (nf y (#prd (∀ x (∀ y P))))
  → (H ⊩ ¬ (∀ (x ⨾ y) P)) → (H ⊩ ¬ (∀ x (∀ y P)));

symbol ALL3 [H x y P R]
  : ⁇ (nf y (#prd (∀ x (∀ y P))))
  → (H ⊩ (∀ (x ⨾ y) P) ⇒ R) → (H ⊩ (∀ x (∀ y P)) ⇒ R);

symbol ALL4 [H x y P]
  : ⁇ (nf y (#prd (∀ x (∀ y P))))
  → (H ⊩ ∀ (x ⨾ y) P) → (H ⊩ ∀ x (∀ y P));

// ALL5: ¬(∀x · P) ⇒ R
// Case 1: x not free in R.
symbol ALL5 [H x P R]
  : ⁇ (pnf x R)
  → (H ⊩ ∀ x (¬ P ⇒ R)) → (H ⊩ ¬ (∀ x P) ⇒ R);

// Case 2: x free in R; y fresh; S = [x := y] P.
symbol ALL5f [H x y] [P S : Prd] [R]
  : ⁇ (pnf y P and pnf y R)
  → ⁇ (psub x (#var y) P == S)
  → (H ⊩ ∀ y (¬ S ⇒ R)) → (H ⊩ ¬ (∀ x P) ⇒ R);

// ALL6: H ⊢ (∀x · P) ⇒ FALSE  ⟹  H ⊢ ¬(∀x · P)
symbol ALL6 [H x P]
  : (H ⊩ (∀ x P) ⇒ FALSE) → (H ⊩ ¬ (∀ x P));

// ALL7: normalisation + promotion of ∀-hypothesis.
// Case 1: x not free in H.
symbol ALL7 [H x P Q]
  : Π R : Res (H ⟝ P),
    (H ⊩ (♢ x (obtain R)) ⇒ Q)
  → (H ⊩ (∀ x P) ⇒ Q);

// Case 2: x free in H; rename.
symbol ALL7f [H x y] [A P : Prd] [Q]
  : ⁇ (pnf y A and pnf y (∀ y A))
  → ⁇ (psub x (#var y) A == P)
  → Π R : Res (H ⟝ P),
    (H ⊩ (♢ x (obtain R)) ⇒ Q)
  → (H ⊩ (∀ x A) ⇒ Q);

// ALL8: proving ∀x · P.
// Case 1: x not free in H.
symbol ALL8 [H x P]
  : ⁇ (pnf x (∀ x P))
  → (H ⊩ P) → (H ⊩ ∀ x P);

// Case 2: x free in H; rename.
symbol ALL8f [H x y] [P R : Prd]
  : ⁇ (pnf y P and pnf y (∀ y P))
  → ⁇ (psub x (#var y) P == R)
  → (H ⊩ R) → (H ⊩ ∀ x P);

// ALL9: final promotion after normalisation.
symbol ALL9 [H x T Q]
  : ((H ∷ ∀ x T) ⊩ Q) → (H ⊩ (♡ x T) ⇒ Q);

// ==== Existential quantification (§A.8) ====

// XST1–XST4: grouping of nested existential quantifications.
symbol XST1 [H x y P R]
  : ⁇ (nf y (#prd (∃ x (∃ y P))))
  → (H ⊩ ¬ (∃ (x ⨾ y) P) ⇒ R) → (H ⊩ ¬ (∃ x (∃ y P)) ⇒ R);

symbol XST2 [H x y P]
  : ⁇ (nf y (#prd (∃ x (∃ y P))))
  → (H ⊩ ¬ (∃ (x ⨾ y) P)) → (H ⊩ ¬ (∃ x (∃ y P)));

symbol XST3 [H x y P R]
  : ⁇ (nf y (#prd (∃ x (∃ y P))))
  → (H ⊩ (∃ (x ⨾ y) P) ⇒ R) → (H ⊩ (∃ x (∃ y P)) ⇒ R);

symbol XST4 [H x y P]
  : ⁇ (nf y (#prd (∃ x (∃ y P))))
  → (H ⊩ ∃ (x ⨾ y) P) → (H ⊩ ∃ x (∃ y P));

// XST5: ¬(∃x · P)  via  ∀x · ¬P.
symbol XST5 [H x P R]
  : (H ⊩ (∀ x (¬ P)) ⇒ R) → (H ⊩ ¬ (∃ x P) ⇒ R);

// XST51: ¬(∃x · ¬P)  via  ∀x · P.
symbol XST51 [H x P R]
  : (H ⊩ (∀ x P) ⇒ R) → (H ⊩ ¬ (∃ x (¬ P)) ⇒ R);

// XST6: H ⊢ ∀x · ¬P  ⟹  H ⊢ ¬(∃x · P)
symbol XST6 [H x P]
  : (H ⊩ ∀ x (¬ P)) → (H ⊩ ¬ (∃ x P));

// XST61: H ⊢ ∀x · P  ⟹  H ⊢ ¬(∃x · ¬P)
symbol XST61 [H x P]
  : (H ⊩ ∀ x P) → (H ⊩ ¬ (∃ x (¬ P)));

// XST7: (∃x · P) ⇒ R  via  ∀x · (P ⇒ R).
// Case 1: x not free in R.
symbol XST7 [H x P R]
  : ⁇ (pnf x R)
  → (H ⊩ ∀ x (P ⇒ R)) → (H ⊩ (∃ x P) ⇒ R);

// Case 2: x free in R; rename.
symbol XST7f [H x y] [P Q : Prd] [R]
  : ⁇ (pnf y P and pnf y R)
  → ⁇ (psub x (#var y) P == Q)
  → (H ⊩ ∀ y (Q ⇒ R)) → (H ⊩ (∃ x P) ⇒ R);

// XST8: proving ∃x · P  via  (∀x · R) ⇒ FALSE.
// Case 1: x not free in H.
symbol XST8 [H x P]
  : Π R : Res (H ⟝ ¬ P),
    (H ⊩ (∀ x (obtain R)) ⇒ FALSE)
  → (H ⊩ ∃ x P);

// Case 2: x free in H; rename.
symbol XST8f [H x y] [A P : Prd]
  : ⁇ (pnf y A and pnf y (∀ y A))
  → ⁇ (psub x (#var y) A == P)
  → Π R : Res (H ⟝ ¬ P),
    (H ⊩ (∀ x (obtain R)) ⇒ FALSE)
  → (H ⊩ ∃ x A);

// ==== Primed (result-producing) variants ====

// ---- ALL primed ----

symbol ALL1' [H x y P R]
  : ⁇ (nf y (#prd (∀ x (∀ y P))))
  → Res (H ⟝ ¬ (∀ (x ⨾ y) P) ⇒ R) → Res (H ⟝ ¬ (∀ x (∀ y P)) ⇒ R)
≔ λ _ ρ, result (obtain ρ);

symbol ALL2' [H x y P]
  : ⁇ (nf y (#prd (∀ x (∀ y P))))
  → Res (H ⟝ ¬ (∀ (x ⨾ y) P)) → Res (H ⟝ ¬ (∀ x (∀ y P)))
≔ λ _ ρ, result (obtain ρ);

symbol ALL3' [H x y P R]
  : ⁇ (nf y (#prd (∀ x (∀ y P))))
  → Res (H ⟝ (∀ (x ⨾ y) P) ⇒ R) → Res (H ⟝ (∀ x (∀ y P)) ⇒ R)
≔ λ _ ρ, result (obtain ρ);

symbol ALL4' [H x y P]
  : ⁇ (nf y (#prd (∀ x (∀ y P))))
  → Res (H ⟝ ∀ (x ⨾ y) P) → Res (H ⟝ ∀ x (∀ y P))
≔ λ _ ρ, result (obtain ρ);

symbol ALL5' [H x P R]
  : ⁇ (pnf x R)
  → Res (H ⟝ ∀ x (¬ P ⇒ R)) → Res (H ⟝ ¬ (∀ x P) ⇒ R)
≔ λ _ ρ, result (obtain ρ);

symbol ALL5f' [H x y] [P S : Prd] [R]
  : ⁇ (pnf y P and pnf y R)
  → ⁇ (psub x (#var y) P == S)
  → Res (H ⟝ ∀ y (¬ S ⇒ R)) → Res (H ⟝ ¬ (∀ x P) ⇒ R)
≔ λ _ _ ρ, result (obtain ρ);

symbol ALL6' [H x P]
  : Res (H ⟝ (∀ x P) ⇒ FALSE) → Res (H ⟝ ¬ (∀ x P))
≔ λ ρ, result (obtain ρ);

// ALL7': (H ⊢ P) ⇝ R; (H ⊢ (♢x · R) ⇒ Q) ⇝ S → result = S
symbol ALL7' [H x P Q]
  : Π R : Res (H ⟝ P),
    Res (H ⟝ (♢ x (obtain R)) ⇒ Q)
  → Res (H ⟝ (∀ x P) ⇒ Q)
≔ λ _ ρ, result (obtain ρ);

symbol ALL7f' [H x y] [A P : Prd] [Q]
  : ⁇ (pnf y A and pnf y (∀ y A))
  → ⁇ (psub x (#var y) A == P)
  → Π R : Res (H ⟝ P),
    Res (H ⟝ (♢ x (obtain R)) ⇒ Q)
  → Res (H ⟝ (∀ x A) ⇒ Q)
≔ λ _ _ _ ρ, result (obtain ρ);

// ALL8': (H ⊢ P) ⇝ Q → result = ∀x · Q
symbol ALL8' [H x P]
  : Res (H ⟝ P) → Res (H ⟝ ∀ x P)
≔ λ ρ, result (∀ x (obtain ρ));

symbol ALL8f' [H x y] [P R : Prd]
  : ⁇ (pnf y P and pnf y (∀ y P))
  → ⁇ (psub x (#var y) P == R)
  → Res (H ⟝ R) → Res (H ⟝ ∀ x P)
≔ λ _ _ ρ, result (∀ y (obtain ρ));

// ALL9': (H, (∀x · P) ⊢ Q) ⇝ R → result = (∀x · P) ⇒ R
symbol ALL9' [H x P Q]
  : Res ((H ∷ ∀ x P) ⟝ Q) → Res (H ⟝ (♡ x P) ⇒ Q)
≔ λ ρ, result ((∀ x P) ⇒ obtain ρ);

// ---- XST primed ----

symbol XST1' [H x y P R]
  : ⁇ (nf y (#prd (∃ x (∃ y P))))
  → Res (H ⟝ ¬ (∃ (x ⨾ y) P) ⇒ R) → Res (H ⟝ ¬ (∃ x (∃ y P)) ⇒ R)
≔ λ _ ρ, result (obtain ρ);

symbol XST2' [H x y P]
  : ⁇ (nf y (#prd (∃ x (∃ y P))))
  → Res (H ⟝ ¬ (∃ (x ⨾ y) P)) → Res (H ⟝ ¬ (∃ x (∃ y P)))
≔ λ _ ρ, result (obtain ρ);

symbol XST3' [H x y P R]
  : ⁇ (nf y (#prd (∃ x (∃ y P))))
  → Res (H ⟝ (∃ (x ⨾ y) P) ⇒ R) → Res (H ⟝ (∃ x (∃ y P)) ⇒ R)
≔ λ _ ρ, result (obtain ρ);

symbol XST4' [H x y P]
  : ⁇ (nf y (#prd (∃ x (∃ y P))))
  → Res (H ⟝ ∃ (x ⨾ y) P) → Res (H ⟝ ∃ x (∃ y P))
≔ λ _ ρ, result (obtain ρ);

symbol XST5' [H x P R]
  : Res (H ⟝ (∀ x (¬ P)) ⇒ R) → Res (H ⟝ ¬ (∃ x P) ⇒ R)
≔ λ ρ, result (obtain ρ);

symbol XST51' [H x P R]
  : Res (H ⟝ (∀ x P) ⇒ R) → Res (H ⟝ ¬ (∃ x (¬ P)) ⇒ R)
≔ λ ρ, result (obtain ρ);

symbol XST6' [H x P]
  : Res (H ⟝ ∀ x (¬ P)) → Res (H ⟝ ¬ (∃ x P))
≔ λ ρ, result (obtain ρ);

symbol XST61' [H x P]
  : Res (H ⟝ ∀ x P) → Res (H ⟝ ¬ (∃ x (¬ P)))
≔ λ ρ, result (obtain ρ);

symbol XST7' [H x P R]
  : ⁇ (pnf x R)
  → Res (H ⟝ ∀ x (P ⇒ R)) → Res (H ⟝ (∃ x P) ⇒ R)
≔ λ _ ρ, result (obtain ρ);

symbol XST7f' [H x y] [P Q : Prd] [R]
  : ⁇ (pnf y P and pnf y R)
  → ⁇ (psub x (#var y) P == Q)
  → Res (H ⟝ ∀ y (Q ⇒ R)) → Res (H ⟝ (∃ x P) ⇒ R)
≔ λ _ _ ρ, result (obtain ρ);

symbol XST8' [H x P]
  : Π R : Res (H ⟝ ¬ P),
    Res (H ⟝ (∀ x (obtain R)) ⇒ FALSE)
  → Res (H ⟝ ∃ x P)
≔ λ _ ρ, result (obtain ρ);

symbol XST8f' [H x y] [A P : Prd]
  : ⁇ (pnf y A and pnf y (∀ y A))
  → ⁇ (psub x (#var y) A == P)
  → Π R : Res (H ⟝ ¬ P),
    Res (H ⟝ (∀ x (obtain R)) ⇒ FALSE)
  → Res (H ⟝ ∃ x A)
≔ λ _ _ _ ρ, result (obtain ρ);
