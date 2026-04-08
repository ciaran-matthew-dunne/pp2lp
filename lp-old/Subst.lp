require open
  pp2lp.B pp2lp.Eq
  pp2lp.NonFree;

// esub rules
// (sequential — order matters).
sequential symbol psub :
  String → Exp → Prd → Prd;
sequential symbol esub :
  String → Exp → Exp → Exp;


// SUB 1: substituting x in
// eid x gives E.
rule esub $x $E (eid $x)
  ↪ $E;
// SUB 2: substituting x in
// eid y (x ≠ y) — unchanged.
rule esub _ _ (eid $y)
  ↪ eid $y;
// esub for pairs (cf. §1.5).
rule esub $x $E ($D ↦ $F)
  ↪ (esub $x $E $D)
    ↦ (esub $x $E $F);
// esub for arithmetic.
rule esub $x $E ($D + $F)
  ↪ (esub $x $E $D)
    + (esub $x $E $F);
rule esub $x $E ($D - $F)
  ↪ (esub $x $E $D)
    - (esub $x $E $F);
rule esub $x $E (⨪ $D)
  ↪ ⨪ (esub $x $E $D);
// esub for constants.
rule esub _ _ 𝟎 ↪ 𝟎;
rule esub _ _ 𝟏 ↪ 𝟏;
rule esub _ _ BTRUE ↪ BTRUE;
rule esub _ _ BFALSE
  ↪ BFALSE;
// esub for functional image.
rule esub $x $E (eapp $f $D)
  ↪ eapp $f
    (esub $x $E $D);

// psub rules
// (sequential — order matters).

// SUB 6/7: quantifier binder.
// If x ∈ vs, shadowed
// (return unchanged).
// Otherwise, sub in body.
symbol ?sub_binder :
  (Prd → Prd) → String →
  Exp → Var → Prd →
  𝔹 → Prd;
rule ?sub_binder
  $Q _ _ _ $P true
  ↪ $Q $P;
rule ?sub_binder
  $Q $x $E _ $P false
  ↪ $Q (psub $x $E $P);

rule psub $x $E
    (pp2lp.B.∀ $vs $P)
  ↪ ?sub_binder
    (pp2lp.B.∀ $vs)
    $x $E $vs $P
    (str_mem $x $vs);
// SUB 3, 4, 5.
rule psub $x $E ($P ∧ $Q)
  ↪ (psub $x $E $P)
    ∧ (psub $x $E $Q);
rule psub $x $E ($P ⇒ $Q)
  ↪ (psub $x $E $P)
    ⇒ (psub $x $E $Q);
rule psub $x $E (¬ $P)
  ↪ ¬ (psub $x $E $P);
// SUB for ∨, ⇔.
rule psub $x $E ($P ∨ $Q)
  ↪ (psub $x $E $P)
    ∨ (psub $x $E $Q);
rule psub $x $E ($P ⇔ $Q)
  ↪ (psub $x $E $P)
    ⇔ (psub $x $E $Q);
// SUB 12.
rule psub $x $E ($D ≃ $F)
  ↪ (esub $x $E $D)
    ≃ (esub $x $E $F);
// SUB for ≤, ≪, eql_set.
rule psub $x $E ($D ≤ $F)
  ↪ (esub $x $E $D)
    ≤ (esub $x $E $F);
rule psub $x $E ($D ≪ $F)
  ↪ (esub $x $E $D)
    ≪ (esub $x $E $F);
rule psub $x $E
    (eql_set $D $F)
  ↪ eql_set
    (esub $x $E $D)
    (esub $x $E $F);
// SUB for constants.
rule psub _ _ TRUE ↪ TRUE;
rule psub _ _ FALSE ↪ FALSE;
// SUB for pred identifiers
// (no vars to substitute).
rule psub _ _ (pid $y)
  ↪ pid $y;
// SUB for pred application:
// substitute in exp arg only.
rule psub $x $E (papp $f $D)
  ↪ papp $f
    (esub $x $E $D);
// SUB for membership:
// substitute in both exps.
rule psub $x $E ($D ∈ $s)
  ↪ (esub $x $E $D)
    ∈ (esub $x $E $s);
// SUB for ∃ (same as ∀).
rule psub $x $E (∃ $vs $P)
  ↪ ?sub_binder
    (∃ $vs) $x $E $vs $P
    (str_mem $x $vs);

// ---- Compound variable substitution ----
// vpsub/vesub generalise psub/esub to
// compound Var, decomposing
//   [(x ⨾ y) := (E ↦ F)]P
// into [x := E]([y := F]P).
symbol vpsub : Var → Exp → Prd → Prd;
symbol vesub : Var → Exp → Exp → Exp;

rule vpsub (id $s) $E $P
  ↪ psub $s $E $P;
rule vpsub ($x ⨾ $y) ($E ↦ $F) $P
  ↪ vpsub $x $E (vpsub $y $F $P);

rule vesub (id $s) $E $D
  ↪ esub $s $E $D;
rule vesub ($x ⨾ $y) ($E ↦ $F) $D
  ↪ vesub $x $E (vesub $y $F $D);
