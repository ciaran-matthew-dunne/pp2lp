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

// ---- INS (§A.11) ----
// No LP symbol — the emitter resolves the instantiation contradiction
// directly from the hypothesis context, emitting:
//   refine !!_to_pi _ h_univ witness (∧ᵢ h₁ … hₙ)
// See translate.ml:find_ins_contradiction.
