// Conjunction (§A.1) — shallow encoding
require open pp2lp.B pp2lp.ConjList pp2lp.Quant pp2lp.rules.Res;

// ---- Base rules ----

// AND1: H ⊢ ¬(last ps) ⇒ R; H ⊢ ¬(init ps) ⇒ R → H ⊢ ¬(⋀ ps) ⇒ R
opaque symbol AND1 [ps : 𝕃 o] [R : Prop]
  : π (¬ ⋀_last (⋀ ps) ⇒ R)
  → π (¬ ⋀_init (⋀ ps) ⇒ R)
  → π (¬ ⋀ ps ⇒ R) ≔
begin
  assume ps R h1 h2 h3;
  have hne : π (¬ (⋀_init (⋀ ps) ∧ ⋀_last (⋀ ps)))
    { assume hpair; refine h3 (⋀_rejoin (∧ₑ₁ hpair) (∧ₑ₂ hpair)) };
  have hor : π (¬ ⋀_init (⋀ ps) ∨ ¬ ⋀_last (⋀ ps))
    { refine =⇒ (deMorgan_∧ (⋀_init (⋀ ps)) (⋀_last (⋀ ps))) hne };
  refine ∨ₑ hor _ _
    { assume hni; refine h2 hni }
    { assume hnl; refine h1 hnl }
end;

// AND2: H ⊢ init ps ⇒ ¬(last ps) → H ⊢ ¬(⋀ ps)
opaque symbol AND2 [ps : 𝕃 o]
  : π (⋀_init (⋀ ps) ⇒ ¬ ⋀_last (⋀ ps))
  → π (¬ ⋀ ps) ≔
begin
  assume ps h1 hc;
  refine h1 (⋀_front hc) (⋀_back hc)
end;

// AND3: H ⊢ init ps ⇒ (last ps ⇒ R) → H ⊢ ⋀ ps ⇒ R
opaque symbol AND3 [ps : 𝕃 o] [R : Prop]
  : π (⋀_init (⋀ ps) ⇒ (⋀_last (⋀ ps) ⇒ R))
  → π (⋀ ps ⇒ R) ≔
begin
  assume ps R h hc;
  refine h (⋀_front hc) (⋀_back hc)
end;

// AND4: H ⊢ last ps; H ⊢ init ps → H ⊢ ⋀ ps
opaque symbol AND4 [ps : 𝕃 o]
  : π (⋀_last (⋀ ps))
  → π (⋀_init (⋀ ps))
  → π (⋀ ps) ≔
begin
  assume ps h1 h2;
  refine ⋀_rejoin h2 h1
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

// AND1_1: Schema 2 — combine two Res children into Res (¬⋀ ps ⇒ R).
symbol AND1_1 [ps : 𝕃 o] [R : Prop]
  (r1 : Res (¬ ⋀_last (⋀ ps) ⇒ R)) (r2 : Res (¬ ⋀_init (⋀ ps) ⇒ R))
  : Res (¬ ⋀ ps ⇒ R)
  ≔ mk_1 (res_tm r1 ∧ res_tm r2)
      (eq_trans and1_eq (conj_eq (res_eq r1) (res_eq r2)));

// AND2_1: Schema 1 — passthrough Res child.
symbol AND2_1 [ps : 𝕃 o]
  (r : Res (⋀_init (⋀ ps) ⇒ ¬ ⋀_last (⋀ ps))) : Res (¬ ⋀ ps)
  ≔ mk_1 (res_tm r) (eq_trans and2_eq (res_eq r));

// AND3_1: Schema 1 — passthrough Res child.
symbol AND3_1 [ps : 𝕃 o] [R : Prop]
  (r : Res (⋀_init (⋀ ps) ⇒ (⋀_last (⋀ ps) ⇒ R))) : Res (⋀ ps ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans and3_eq (res_eq r));

// AND4_1: Schema 2 — combine two Res children into Res (⋀ ps).
// `⋀_join (last init)` reduces to `last ∧ init`, matching the order
// downstream NRM rules expect when they decompose the result chain's
// conclusion.
symbol AND4_1 [ps : 𝕃 o]
  (r1 : Res (⋀_last (⋀ ps))) (r2 : Res (⋀_init (⋀ ps))) : Res (⋀ ps)
  ≔ mk_1 (⋀_join (res_tm r1) (res_tm r2))
           (eq_trans ⋀_split
             (eq_trans (∧_com (⋀_init (⋀ ps)) (⋀_last (⋀ ps)))
               (conj_eq (res_eq r1) (res_eq r2))));

// AND5_1: Schema 1 with antecedent congruence on the implication's LHS.
// Mirrors AND5's PP shape: an extraction `fwd : π C → π C'` plus its
// inverse `bwd` build the propositional equality on antecedents.
symbol AND5_1 [C C' r : Prop]
  (fwd : π C → π C') (bwd : π C' → π C) (rr : Res (C' ⇒ r))
  : Res (C ⇒ r)
  ≔ mk_1 (res_tm rr) (eq_trans (ante_cong fwd bwd) (res_eq rr));
