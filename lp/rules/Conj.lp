// Conjunction (§A.1) — shallow encoding
require open pp2lp.B pp2lp.ConjList;

// ---- Base rules ----

// AND1: H ⊢ ¬(last ps) ⇒ R; H ⊢ ¬(init ps) ⇒ R → H ⊢ ¬(⋀ ps) ⇒ R
opaque symbol AND1 [ps : 𝕃 o] [R : Prop]
  : π (¬ (last ⊤ ps) ⇒ R)
  → π (¬ ⋀_init (⋀ ps) ⇒ R)
  → π (¬ ⋀ ps ⇒ R) ≔
begin
  assume ps R h1 h2 h3;
  have hne : π (¬ (⋀_init (⋀ ps) ∧ last ⊤ ps))
    { assume hpair; refine h3 (⋀_rejoin (∧ₑ₁ hpair) (∧ₑ₂ hpair)) };
  have hor : π (¬ ⋀_init (⋀ ps) ∨ ¬ (last ⊤ ps))
    { refine =⇒ (deMorgan_∧ (⋀_init (⋀ ps)) (last ⊤ ps)) hne };
  refine ∨ₑ hor _ _
    { assume hni; refine h2 hni }
    { assume hnl; refine h1 hnl }
end;

// AND2: H ⊢ init ps ⇒ ¬(last ps) → H ⊢ ¬(⋀ ps)
opaque symbol AND2 [ps : 𝕃 o]
  : π (⋀_init (⋀ ps) ⇒ ¬ (last ⊤ ps))
  → π (¬ ⋀ ps) ≔
begin
  assume ps h1 hc;
  refine h1 (⋀_front hc) (⋀_back hc)
end;

// AND3: H ⊢ init ps ⇒ (last ps ⇒ R) → H ⊢ ⋀ ps ⇒ R
opaque symbol AND3 [ps : 𝕃 o] [R : Prop]
  : π (⋀_init (⋀ ps) ⇒ (last ⊤ ps ⇒ R))
  → π (⋀ ps ⇒ R) ≔
begin
  assume ps R h hc;
  refine h (⋀_front hc) (⋀_back hc)
end;

// AND4: H ⊢ last ps; H ⊢ init ps → H ⊢ ⋀ ps
opaque symbol AND4 [ps : 𝕃 o]
  : π (last ⊤ ps)
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
