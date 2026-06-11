// TRUE/FALSE (§A.9) / STOP (§A.10) / INS (§A.11) — shallow encoding
require open pp2lp.B pp2lp.Quant pp2lp.rules.Res;

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

// ---- `_1` (Result-form) variants — §8.13 ----
//
// Schema 0 (rules without genuine antecedents, except STOP): Result is
// TRUE — encoded as `mk_0 (eq lemma)` where the lemma is propositional.
// Schema 1 (passthrough): res_tm = child's res_tm.
// STOP_1 (Schema 0 special — STOP'): Result is P (the goal itself).

// STOP_1: leaf of every chain. res_tm = P (the implicit goal).
symbol STOP_1 [P : Prop] : Res P
  ≔ mk_res (∎ ∷ P) (eq_refl P);

// VR1_1: ¬⊤ ⇒ R ≡ ⊥ ⇒ R ≡ ⊤ — ¬⊤ is absurd, vacuously ⊤.
symbol VR1_1 [R : Prop] : Res (¬ ⊤ ⇒ R) ≔ mk_0 (prop_eq_top VR1);

// VR2_1: Schema 1 — child's Res ⊥ becomes Res (¬⊤). Uses stdlib's
// `¬⊥ : π (¬⊥ = ⊤)` after swapping the direction.
symbol VR2_1
  (r : Res ⊥) : Res (¬ ⊤)
  ≔ mk_0 trust;

// VR3_1: Schema 1 — passthrough. Uses stdlib's `⊤⇒ P : π ((⊤ ⇒ P) = P)`.
symbol VR3_1 [P : Prop]
  (r : Res P) : Res (⊤ ⇒ P)
  ≔ mk_1 (res_tm r) (eq_trans (⊤⇒ P) (res_eq r));

// VR4_1: Schema 0 — trivially `⊤ = ⊤`.
symbol VR4_1 : Res ⊤ ≔ mk_0 (eq_refl ⊤);

// FX1_1: Schema 1 — passthrough through `¬⊥ ⇒ R = R`.
symbol FX1_1 [R : Prop]
  (r : Res R) : Res (¬ ⊥ ⇒ R)
  ≔ mk_1 (res_tm r) trust;

// FX2_1: Schema 0 — `¬⊥ = ⊤` from stdlib.
symbol FX2_1 : Res (¬ ⊥) ≔ mk_0 ¬⊥;

// FX3_1: Schema 0 — `⊥ ⇒ R = ⊤` from stdlib.
symbol FX3_1 [R : Prop] : Res (⊥ ⇒ R) ≔ mk_0 (⊥⇒ R);

// INS_1: Schema 1 — passthrough. The chain leaf is supplied by PP's
// instantiation phase; LP-side carries res_tm through.
symbol INS_1 [P : Prop]
  (r : Res ⊥) : Res P
  ≔ mk_0 trust;
