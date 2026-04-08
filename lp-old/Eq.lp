require open pp2lp.B;

// syntactic equality.
sequential symbol str_eq :
  String → String → 𝔹;
rule str_eq $s $s ↪ true
with str_eq _ _   ↪ false;

// variable equality:
// structural string-list cmp.
sequential symbol veq :
  Var → Var → 𝔹;
rule veq (id $s) (id $s')
  ↪ str_eq $s $s'
with veq ($x ⨾ $y) ($x' ⨾ $y')
  ↪ (veq $x $x') and (veq $y $y')
with veq (id _) (_ ⨾ _) ↪ false
with veq (_ ⨾ _) (id _) ↪ false;

symbol vneq (x y : Var) ≔ not (veq x y);

// expression equality.
sequential symbol exp_eq :
  Exp → Exp → 𝔹;
sequential symbol prd_eq :
  Prd → Prd → 𝔹;
rule exp_eq (eid $x) (eid $y)
  ↪ str_eq $x $y
with exp_eq
    ($E ↦ $F) ($G ↦ $H)
  ↪ (exp_eq $E $G)
    and (exp_eq $F $H)
with exp_eq 𝟎 𝟎 ↪ true
with exp_eq 𝟏 𝟏 ↪ true
with exp_eq BTRUE BTRUE
  ↪ true
with exp_eq BFALSE BFALSE
  ↪ true
with exp_eq
    ($x1 + $x2) ($y1 + $y2)
  ↪ (exp_eq $x1 $y1)
    and (exp_eq $x2 $y2)
with exp_eq
    ($x1 - $x2) ($y1 - $y2)
  ↪ (exp_eq $x1 $y1)
    and (exp_eq $x2 $y2)
with exp_eq (⨪ $x) (⨪ $y)
  ↪ (exp_eq $x $y)
with exp_eq
    (eapp $f $E) (eapp $g $F)
  ↪ (str_eq $f $g)
    and (exp_eq $E $F)
with exp_eq $e $e ↪ true
with exp_eq _ _ ↪ false
with prd_eq
    ($p ∧ $q) ($r ∧ $s)
  ↪ (prd_eq $p $r)
    and (prd_eq $q $s)
with prd_eq
    ($p ∨ $q) ($r ∨ $s)
  ↪ (prd_eq $p $r)
    and (prd_eq $q $s)
with prd_eq
    ($p ⇒ $q) ($r ⇒ $s)
  ↪ (prd_eq $p $r)
    and (prd_eq $q $s)
with prd_eq
    ($p ⇔ $q) ($r ⇔ $s)
  ↪ (prd_eq $p $r)
    and (prd_eq $q $s)
with prd_eq (¬ $p) (¬ $q)
  ↪ (prd_eq $p $q)
with prd_eq (pid $x) (pid $y)
  ↪ str_eq $x $y
with prd_eq
    (∀ $x $p) (∀ $y $q)
  ↪ (veq $x $y)
    and (prd_eq $p $q)
with prd_eq
    (∃ $x $p) (∃ $y $q)
  ↪ (veq $x $y)
    and (prd_eq $p $q)
with prd_eq
    (♢ $x $p) (♢ $y $q)
  ↪ (veq $x $y)
    and (prd_eq $p $q)
with prd_eq
    (♡ $x $p) (♡ $y $q)
  ↪ (veq $x $y)
    and (prd_eq $p $q)
with prd_eq
    ($e ≃ $f) ($g ≃ $h)
  ↪ (exp_eq $e $g)
    and (exp_eq $f $h)
with prd_eq
    (eql_set $e $f)
    (eql_set $g $h)
  ↪ (exp_eq $e $g)
    and (exp_eq $f $h)
with prd_eq
    ($e ≤ $f) ($g ≤ $h)
  ↪ (exp_eq $e $g)
    and (exp_eq $f $h)
with prd_eq
    ($e ≪ $f) ($g ≪ $h)
  ↪ (exp_eq $e $g)
    and (exp_eq $f $h)

with prd_eq
    (papp $f $E) (papp $g $F)
  ↪ (str_eq $f $g)
    and (exp_eq $E $F)
with prd_eq
    ($E ∈ $s) ($F ∈ $t)
  ↪ (exp_eq $E $F)
    and (exp_eq $s $t)
with prd_eq TRUE TRUE ↪ true
with prd_eq FALSE FALSE
  ↪ true
with prd_eq _ _ ↪ false;
