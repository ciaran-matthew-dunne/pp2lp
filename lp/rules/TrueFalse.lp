// TRUE/FALSE (§A.9) / STOP (§A.10) / INS (§A.11) — shallow encoding
require open pp2lp.B;

// ---- TRUE (§A.9) ----

// VR1: H ⊢ ¬TRUE ⇒ R
opaque symbol VR1 [R]
  : π (¬ ⊤ ⇒ R) ≔
begin
  assume R h;
  refine ⊥ₑ (h ⊤ᵢ)
end;

// VR2: H ⊢ FALSE → H ⊢ ¬TRUE
opaque symbol VR2
  : π ⊥
  → π (¬ ⊤) ≔
begin
  assume h h0; refine h
end;

// VR3: H ⊢ R → H ⊢ TRUE ⇒ R
opaque symbol VR3 [R]
  : π R
  → π (⊤ ⇒ R) ≔
begin
  assume R h h0; refine h
end;

// VR4: H ⊢ TRUE
opaque symbol VR4
  : π ⊤ ≔
begin
  refine ⊤ᵢ
end;

// ---- FALSE ----

// FX1: H ⊢ R → H ⊢ ¬FALSE ⇒ R
opaque symbol FX1 [R]
  : π R
  → π (¬ ⊥ ⇒ R) ≔
begin
  assume R h h0; refine h
end;

// FX2: H ⊢ ¬FALSE
opaque symbol FX2
  : π (¬ ⊥) ≔
begin
  assume h; refine h
end;

// FX3: H ⊢ FALSE ⇒ R
opaque symbol FX3 [R]
  : π (⊥ ⇒ R) ≔
begin
  assume R h; refine ⊥ₑ h
end;

// ---- STOP (§A.10) ----

// STOP: P is not FALSE; H ⊢ ¬P ⇒ FALSE → H ⊢ P
opaque symbol STOP [P]
  : π (¬ P ⇒ ⊥)
  → π P ≔
begin
  assume P h; refine ¬¬ₑ P h
end;

// ---- Primed variants (equality-based) ----
// Results are predicates equivalent to the consequent.
// STOP_1: result = P (reflexivity).
// Schema 0 (leaf): result = ⊤ (the goal is a tautology).
// Schema 1 (pass-through): consequent = antecedent, so transitivity.

opaque symbol STOP_1 [P : Prop]
  : π (P = P) ≔
begin
  assume P; reflexivity
end;

// VR1_1: result = ⊤. ¬⊤⇒R is a tautology (¬⊤ is ⊥).
opaque symbol VR1_1 [R : Prop]
  : π ((¬ ⊤ ⇒ R) = ⊤) ≔
begin
  assume R; rewrite ¬⊤; refine ⊥⇒ R
end;

// VR2_1: pass-through. ¬⊤ = ⊥.
opaque symbol VR2_1 [S : Prop]
  : π (⊥ = S)
  → π (¬ ⊤ = S) ≔
begin
  assume S h; rewrite ¬⊤; refine h
end;

// VR3_1: pass-through. (⊤ ⇒ R) = R.
opaque symbol VR3_1 [R S : Prop]
  : π (R = S)
  → π ((⊤ ⇒ R) = S) ≔
begin
  assume R S h; rewrite ⊤⇒; refine h
end;

// VR4_1: result = ⊤. ⊤ = ⊤.
opaque symbol VR4_1
  : π (⊤ = ⊤) ≔
begin
  reflexivity
end;

// FX1_1: pass-through. (¬⊥ ⇒ R) = R.
opaque symbol FX1_1 [R S : Prop]
  : π (R = S)
  → π ((¬ ⊥ ⇒ R) = S) ≔
begin
  assume R S h; rewrite ¬⊥; rewrite ⊤⇒; refine h
end;

// FX2_1: result = ⊤. ¬⊥ = ⊤.
opaque symbol FX2_1
  : π (¬ ⊥ = ⊤) ≔
begin
  refine ¬⊥
end;

// FX3_1: result = ⊤. (⊥ ⇒ R) = ⊤.
opaque symbol FX3_1 [R : Prop]
  : π ((⊥ ⇒ R) = ⊤) ≔
begin
  assume R; refine ⊥⇒ R
end;

// ---- INS (§A.11) ----

// INS: Determination of instantiations Q₁,...,Qₙ;
//      H ⊢ Q₁ ⇒ (Q₂ ⇒ ... (Qₙ ⇒ FALSE)...) → H ⊢ FALSE
// The emitter resolves INS dynamically by finding the contradicting
// hypotheses (¬P and P) in context and applying modus ponens.
// The INS LP symbol is not used directly — kept for reference.
opaque symbol INS [P Q : Prop]
  : π P
  → π (P ⇒ Q)
  → π Q ≔
begin
  assume P Q hp hpq; refine hpq hp
end;
