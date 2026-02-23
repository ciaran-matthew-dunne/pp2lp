require open pp2lp.B;

// NF 1.
rule enf $x (#var $y) ↪ var_eq $x $y;

// NF 2, 3, 4.
rule pnf $x ($P ∧ $Q) ↪ (pnf $x $P) and (pnf $x $Q)
with pnf $x ($P ⇒ $Q) ↪ (pnf $x $P) and (pnf $x $Q)
with pnf $x (¬ $P) ↪ pnf $x $P;

// NF 5, 6.
rule pnf $x (∀ $x $P) ↪ true
with pnf $x (∀ $y $P) ↪ (enf $x (#var $y)) and (pnf $x $P);

// NF 7, 8.
rule enf $x (esub $x $E _) ↪ enf $x $E
with enf $x (esub $y $E $F)
  ↪ (enf $x (#var $y)) and (enf $x $E) and (enf $x $F);

// NF 9.
rule pnf $x ($E = $F) ↪ (enf $x $E) and (enf $x $F);

// NF 10, 11.
rule enf ($x ⨾ $y) $E ↪ (enf $x $E) and (enf $y $E)
with enf $x ($E ↦ $F) ↪ (enf $x $E) and (enf $x $F);

// NF 12.
rule pnf $x (∀ ($y ⨾ $z) $P) ↪ pnf $x (∀ $y (∀ $z $P));

// NF 13.
rule pnf $x ($E ∈ $s) ↪ (enf $x $E) and (enf $x $s);

// NF 14.
rule enf $x (choice $s) ↪ enf $x $s;

// NF 15, 16.
rule enf $x ($s × $t) ↪ (enf $x $s) and (enf $x $t)
with enf $x (𝒫 $s) ↪ enf $x $s;

// NF 17.
rule enf $x (comp $x $P) ↪ true
with enf $x (comp $y $P) ↪ (enf $x (#var $y)) and (pnf $x $P);

// NF 18.
rule enf _ big ↪ true;
