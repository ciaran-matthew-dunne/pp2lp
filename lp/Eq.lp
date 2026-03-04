require open pp2lp.B;

// variable equality: uses meta-level identity for `id` (no string equality
// available), and structural recursion for `⨾`.
rule var_eq (id $s) (id $s) ↪ true
with var_eq ($x ⨾ $y) ($z ⨾ $w) ↪ (var_eq $x $z) and (var_eq $y $w)
with var_eq _ _ ↪ false;

// expression equality.
rule exp_eq (#var $x) (#var $y) ↪ var_eq $x $y
with exp_eq ($E ↦ $F) ($G ↦ $H)
  ↪ (exp_eq $E $G) and (exp_eq $F $H)
with exp_eq (choice $s) (choice $t) ↪ exp_eq $s $t
with exp_eq ($s × $t) ($u × $v)
  ↪ (exp_eq $s $u) and (exp_eq $t $v)
with exp_eq (𝒫 $s) (𝒫 $t) ↪ exp_eq $s $t
with exp_eq (big) (big) ↪ true
with exp_eq (comp $x $P) (comp $y $Q)
  ↪ (var_eq $x $y) and (prd_eq $P $Q)
with exp_eq _ _ ↪ false;

// predicate equality.
rule prd_eq ($p ∧ $q) ($r ∧ $s)
  ↪ (prd_eq $p $r) and (prd_eq $q $s)
with prd_eq ($p ∨ $q) ($r ∨ $s)
  ↪ (prd_eq $p $r) and (prd_eq $q $s)
with prd_eq ($p ⇒ $q) ($r ⇒ $s)
  ↪ (prd_eq $p $r) and (prd_eq $q $s)
with prd_eq ($p ⇔ $q) ($r ⇔ $s)
  ↪ (prd_eq $p $r) and (prd_eq $q $s)
with prd_eq (¬ $p) (¬ $q)
  ↪ (prd_eq $p $q)
with prd_eq (∀ $x $p) (∀ $y $q)
  ↪ (var_eq $x $y) and (prd_eq $p $q)
with prd_eq (∃ $x $p) (∃ $y $q)
  ↪ (var_eq $x $y) and (prd_eq $p $q)
with prd_eq (♢ $x $p) (♢ $y $q)
  ↪ (var_eq $x $y) and (prd_eq $p $q)
with prd_eq (♡ $x $p) (♡ $y $q)
  ↪ (var_eq $x $y) and (prd_eq $p $q)
with prd_eq ($e = $f) ($g = $h)
  ↪ (exp_eq $e $g) and (exp_eq $f $h)
with prd_eq ($e ∈ $s) ($f ∈ $t)
  ↪ (exp_eq $e $f) and (exp_eq $s $t)
with prd_eq _ _ ↪ false;
