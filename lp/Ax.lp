require open pp2lp.B;

// SET 1.
constant symbol SET1 [E F s t] :
  prf ((E ↦ F) ∈ (s × t) ⇔ E ∈ s ∧ F ∈ t);

// SET 2.
constant symbol SET2 [x : Var] [s t] :
  prf (s ∈ 𝒫 t ⇔ ∀ x (x ∈ s ⇒ x ∈ t));

// SET 3.
constant symbol SET3 [x : Var] [E s P] :
  prf (E ∈ comp x (x ∈ s ∧ P) ⇔ E ∈ s ∧ psub x E P);

// SET 4.
constant symbol SET4 [x : Var] [s t] :
  prf (∀ x (x ∈ s ⇔ x ∈ t) ⇒ s = t);

// SET 5.
constant symbol SET5 [x : Var] [s] :
  prf (¬ (∀ x (¬ (x ∈ s))) ⇒ choice s ∈ s);

// SET 6: infinite(BIG).
// Requires a definition of `infinite` (Ch. 3); omitted for now.
