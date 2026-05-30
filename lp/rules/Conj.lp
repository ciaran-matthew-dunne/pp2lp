// Conjunction (§A.1) — shallow encoding over the snoc list 𝕃*.
//
// PP's ∧ is left-associative, so a conjunction goal `⋀ (ps ∷ P)` splits
// structurally: init = `⋀ ps`, last = `P`.  Each rule pattern-matches the
// `∷` directly; Lambdapi infers `ps`/`P` from the goal (via the `⋀`
// unification rule in ConjList.lp).
require open pp2lp.B pp2lp.ConjList pp2lp.Quant pp2lp.rules.Res;

// ---- Base rules ----

// AND1: H ⊢ ¬P ⇒ R; H ⊢ ¬⋀ps ⇒ R → H ⊢ ¬⋀(ps∷P) ⇒ R
opaque symbol AND1 [ps : 𝕃* o] [P R : Prop]
  : π (¬ P ⇒ R)
  → π (¬ ⋀ ps ⇒ R)
  → π (¬ ⋀ (ps ∷ P) ⇒ R) ≔
begin
  assume ps P R h1 h2 h3;
  have hnand : π (¬ (⋀ ps ∧ P))
    { assume hand; refine h3 (⋀_intro (∧ₑ₁ hand) (∧ₑ₂ hand)) };
  have hor : π (¬ ⋀ ps ∨ ¬ P)
    { refine =⇒ (deMorgan_∧ (⋀ ps) P) hnand };
  refine ∨ₑ hor _ _
    { assume hni; refine h2 hni }
    { assume hnp; refine h1 hnp }
end;

// AND2: H ⊢ ⋀ps ⇒ ¬P → H ⊢ ¬⋀(ps∷P)
opaque symbol AND2 [ps : 𝕃* o] [P : Prop]
  : π (⋀ ps ⇒ ¬ P)
  → π (¬ ⋀ (ps ∷ P)) ≔
begin
  assume ps P h1 hc;
  refine h1 (⋀_init hc) (⋀_last hc)
end;

// AND3: H ⊢ ⋀ps ⇒ (P ⇒ R) → H ⊢ ⋀(ps∷P) ⇒ R
opaque symbol AND3 [ps : 𝕃* o] [P R : Prop]
  : π (⋀ ps ⇒ (P ⇒ R))
  → π (⋀ (ps ∷ P) ⇒ R) ≔
begin
  assume ps P R h hc;
  refine h (⋀_init hc) (⋀_last hc)
end;

// AND4: H ⊢ P; H ⊢ ⋀ps → H ⊢ ⋀(ps∷P)   (PP order: last then init)
opaque symbol AND4 [ps : 𝕃* o] [P : Prop]
  : π P
  → π (⋀ ps)
  → π (⋀ (ps ∷ P)) ≔
begin
  assume ps P h1 h2;
  refine ⋀_intro h2 h1
end;

// AND5: modus ponens within a conjunction.
opaque symbol AND5 [C C' r : Prop]
  : (π C → π C')
  → π (C' ⇒ r)
  → π (C ⇒ r) ≔
begin
  assume C C' r fwd hsub hc;
  refine hsub (fwd hc)
end;

// ---- `_1` (Result-form) variants — §8.13 ----

// AND1_1: Schema 2 — combine two Res children into Res (¬⋀(ps∷P) ⇒ R).
symbol AND1_1 [ps : 𝕃* o] [P R : Prop]
  (r1 : Res (¬ P ⇒ R)) (r2 : Res (¬ ⋀ ps ⇒ R))
  : Res (¬ ⋀ (ps ∷ P) ⇒ R)
  ≔ mk_res (concat (res_ts r1) (res_ts r2))
      (eq_trans and1_eq
        (eq_trans (conj_eq (res_eq r1) (res_eq r2))
                  (conj_concat_eq (res_ts r1) (res_ts r2))));

// AND2_1: Schema 1 — passthrough Res child.
symbol AND2_1 [ps : 𝕃* o] [P : Prop]
  (r : Res (⋀ ps ⇒ ¬ P)) : Res (¬ ⋀ (ps ∷ P))
  ≔ mk_1 (res_tm r) (eq_trans and2_eq (res_eq r));

// AND3_1: Schema 1 — passthrough Res child.
symbol AND3_1 [ps : 𝕃* o] [P R : Prop]
  (r : Res (⋀ ps ⇒ (P ⇒ R))) : Res (⋀ (ps ∷ P) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans and3_eq (res_eq r));

// AND4_1: Schema 2 — combine two Res children into Res (⋀ (ps ∷ P)).
// `and4_eq` reorders `⋀ (ps ∷ P)` to the last-first binary `P ∧ ⋀ ps`,
// then it follows the same `conj_eq`/`conj_concat_eq` chain as every combine.
symbol AND4_1 [ps : 𝕃* o] [P : Prop]
  (r1 : Res P) (r2 : Res (⋀ ps)) : Res (⋀ (ps ∷ P))
  ≔ mk_res (concat (res_ts r1) (res_ts r2))
      (eq_trans and4_eq
        (eq_trans (conj_eq (res_eq r1) (res_eq r2))
                  (conj_concat_eq (res_ts r1) (res_ts r2))));

// AND5_1: Schema 1 with antecedent congruence on the implication's LHS.
// Mirrors AND5's PP shape: an extraction `fwd : π C → π C'` plus its
// inverse `bwd` build the propositional equality on antecedents.
symbol AND5_1 [C C' r : Prop]
  (fwd : π C → π C') (bwd : π C' → π C) (rr : Res (C' ⇒ r))
  : Res (C ⇒ r)
  ≔ mk_1 (res_tm rr) (eq_trans (ante_cong fwd bwd) (res_eq rr));
