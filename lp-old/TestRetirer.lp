require open pp2lp.Rules;

// Test retirer on a simple case
symbol test_retirer :
  ⁇ (prd_eq
    (retirer (("f" ≃ "TRUE") ⇒ (("d" ≃ "e") ∧ ("g" ≃ "TRUE")))
            (((((((("f" ≃ "TRUE") ⇒ (("d" ≃ "e") ∧ ("g" ≃ "TRUE")))
              ∧ "C2") ∧ "C3") ∧ "C4") ∧ "C5") ∧ "C6") ∧ "C7"))
    (((((("C2" ∧ "C3") ∧ "C4") ∧ "C5") ∧ "C6") ∧ "C7")))
  ≔ ⊤ᵢ;
