require open pp2lp.B;

// SUB 1, 2.
rule esub $x $E (#var $x) ↪ $E
with esub $x $E (#var $y) ↪ ?exp (#var $y) (enf $x (#var $y));

// SUB 3, 4, 5.
rule psub $x $E ($P ∧ $Q) ↪ (psub $x $E $P) ∧ (psub $x $E $Q)
with psub $x $E ($P ⇒ $Q) ↪ (psub $x $E $P) ⇒ (psub $x $E $Q)
with psub $x $E (¬ $P) ↪ ¬ (psub $x $E $P);

// SUB 6, 7.
rule psub $x _ (∀ $x $P) ↪ ∀ $x $P
with psub $x $E (∀ $y $P)
  ↪ ?prd (∀ $y (psub $x $E $P)) (enf $x (#var $y));

// SUB 12.
rule psub $x $E ($D = $F)
  ↪ (esub $x $E $D) = (esub $x $E $F);

// esub for pairs (cf. §1.5).
rule esub $x $E ($D ↦ $F)
  ↪ (esub $x $E $D) ↦ (esub $x $E $F);

// SUB 14.
rule psub $x $E ($F ∈ $s)
  ↪ (esub $x $E $F) ∈ (esub $x $E $s);

// SUB 15.
rule esub $x $E (choice $s) ↪ choice (esub $x $E $s);

// SUB 16, 17.
rule esub $x $E ($s × $t) ↪ (esub $x $E $s) × (esub $x $E $t)
with esub $x $E (𝒫 $s) ↪ 𝒫 (esub $x $E $s);

// SUB 18, 19.
rule esub $x _ (comp $x $P) ↪ comp $x $P
with esub $x $E (comp $y $P)
  ↪ ?exp (comp $y (psub $x $E $P)) (enf $x (#var $y));

// SUB 20.
rule esub _ _ big ↪ big;
