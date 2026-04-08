require open pp2lp.B pp2lp.Eq;

// str_mem: is string s a member
// of compound variable vs?
sequential symbol str_mem :
  String → Var → 𝔹;
rule str_mem $s (id $s')
  ↪ str_eq $s $s'
with str_mem $s ($x ⨾ $y)
  ↪ (str_mem $s $x)
    or (str_mem $s $y);

// vnf: is string s in every
// leaf of variable x?
sequential symbol vnf :
  String → Var → 𝔹;
rule vnf $s (id $s')
  ↪ str_eq $s $s'
with vnf $s ($x ⨾ $y)
  ↪ (vnf $s $x)
    and (vnf $s $y);

// non-freeness checks.
sequential symbol pnf :
  String → Prd → 𝔹;
sequential symbol enf :
  String → Exp → 𝔹;
sequential symbol vpnf :
  Var → Prd → 𝔹;
sequential symbol venf :
  Var → Exp → 𝔹;

rule vpnf (id $s) $P
  ↪ pnf $s $P
with vpnf ($x ⨾ $y) $P
  ↪ (vpnf $x $P) and (vpnf $y $P);

rule venf (id $s) $E
  ↪ enf $s $E
with venf ($x ⨾ $y) $E
  ↪ (venf $x $E)
    and (venf $y $E);

// NF 5/6: quantifier binder.
// If x is in the binder list,
// it's shadowed (true).
// Otherwise, check the body.
// Uses ?𝔹 to branch.
symbol ?𝔹 : 𝔹 → 𝔹 → 𝔹;
rule ?𝔹 _ true ↪ true
with ?𝔹 $b false ↪ $b;

rule pnf $x (∀ $vs $P)
  ↪ ?𝔹 (pnf $x $P)
    (str_mem $x $vs);
// NF 2, 3, 4.
rule pnf $x ($P ∧ $Q)
  ↪ (pnf $x $P)
    and (pnf $x $Q);
rule pnf $x ($P ⇒ $Q)
  ↪ (pnf $x $P)
    and (pnf $x $Q);
rule pnf $x (¬ $P)
  ↪ pnf $x $P;
// NF 9: equality.
rule pnf $x ($E ≃ $F)
  ↪ (enf $x $E)
    and (enf $x $F);
// NF for ∨, ⇔.
rule pnf $x ($P ∨ $Q)
  ↪ (pnf $x $P)
    and (pnf $x $Q);
rule pnf $x ($P ⇔ $Q)
  ↪ (pnf $x $P)
    and (pnf $x $Q);
// NF for ≤, ≪.
rule pnf $x ($E ≤ $F)
  ↪ (enf $x $E)
    and (enf $x $F);
rule pnf $x ($E ≪ $F)
  ↪ (enf $x $E)
    and (enf $x $F);
// NF for eql_set.
rule pnf $x (eql_set $E $F)
  ↪ (enf $x $E)
    and (enf $x $F);
// NF for constants.
rule pnf _ TRUE ↪ true;
rule pnf _ FALSE ↪ true;
// NF for predicate identifiers.
rule pnf $x (pid $y)
  ↪ not (str_eq $x $y);
// NF for pred application:
// check name and exp argument.
rule pnf $x (papp $f $E)
  ↪ (not (str_eq $x $f))
    and (enf $x $E);
// NF for membership:
// check both exp and set exp.
rule pnf $x ($E ∈ $s)
  ↪ (enf $x $E)
    and (enf $x $s);
// NF for ∃ (same as ∀).
rule pnf $x (∃ $vs $P)
  ↪ ?𝔹 (pnf $x $P)
    (str_mem $x $vs);
// NF for ♢, ♡ (same as ∀).
rule pnf $x (♢ $vs $P)
  ↪ ?𝔹 (pnf $x $P)
    (str_mem $x $vs);
rule pnf $x (♡ $vs $P)
  ↪ ?𝔹 (pnf $x $P)
    (str_mem $x $vs);

// enf rules
// (sequential — order matters).

// NF 1: x not free in eid y
// iff x ≠ y.
rule enf $x (eid $y)
  ↪ not (str_eq $x $y);
// NF 11: pair.
rule enf $x ($E ↦ $F)
  ↪ (enf $x $E)
    and (enf $x $F);
// NF for arithmetic.
rule enf $x ($E + $F)
  ↪ (enf $x $E)
    and (enf $x $F);
rule enf $x ($E - $F)
  ↪ (enf $x $E)
    and (enf $x $F);
rule enf $x (⨪ $E)
  ↪ enf $x $E;
// NF for constants.
rule enf _ 𝟎 ↪ true;
rule enf _ 𝟏 ↪ true;
rule enf _ BTRUE ↪ true;
rule enf _ BFALSE ↪ true;
// NF for functional image:
// check name and exp argument.
rule enf $x (eapp $f $E)
  ↪ (not (str_eq $x $f))
    and (enf $x $E);
