// Existential quantification (§A.8) — shallow encoding
//
// With HOAS:
// - Variable renaming (XST7f, XST8f) collapses into XST7, XST8.
// - Compound variables (XST1-4) don't exist; nested ∃ IS
//   the only form. The OCaml emitter should skip XST1-4.
require open pp2lp.B;

// ---- Identity rules (compound variable flattening) ----
//
// XST7f, XST8f: Variable renaming variants of XST7, XST8.
//   In HOAS, α-equivalence is automatic, so these collapse
//   into their base forms.

// XST1: ¬(∃(x,y)·P) ⇒ R → ¬(∃x·∃y·P) ⇒ R (identity in HOAS)
opaque symbol XST1 [P : τ ι → τ ι → Prop] [R : Prop] (nf : π ⊤)
  : π (¬ (`∃ x, `∃ y, P x y) ⇒ R)
  → π (¬ (`∃ x, `∃ y, P x y) ⇒ R) ≔
begin assume P R nf h; refine h end;

// XST2: ∃(x,y)·P ⇒ R → ∃x·∃y·P ⇒ R (identity in HOAS)
opaque symbol XST2 [P : τ ι → τ ι → Prop] [R : Prop] (nf : π ⊤)
  : π ((`∃ x, `∃ y, P x y) ⇒ R)
  → π ((`∃ x, `∃ y, P x y) ⇒ R) ≔
begin assume P R nf h; refine h end;

// XST3: Compound ∃ flattening (identity in HOAS).
// Used both with and without ∧ context.
opaque symbol XST3 [P : τ ι → τ ι → Prop] [R : Prop] (nf : π ⊤)
  : π ((`∃ x, `∃ y, P x y) ⇒ R)
  → π ((`∃ x, `∃ y, P x y) ⇒ R) ≔
begin assume P R nf h; refine h end;

opaque symbol XST4 [P : τ ι → τ ι → Prop](nf : π ⊤)
  : π (`∃ x, `∃ y, P x y)
  → π (`∃ x, `∃ y, P x y) ≔
begin assume P nf h; refine h end;

// ---- Base rules ----

// XST5: H ⊢ (∀x·¬P) ⇒ R → H ⊢ ¬(∃x·P) ⇒ R
opaque symbol XST5 [P : τ ι → Prop] [R : Prop]
  : π ((`∀ x, ¬ (P x)) ⇒ R)
  → π (¬ (`∃ x, P x) ⇒ R) ≔
begin
  assume P R h1 h2;
  refine h1 (λ x hpx, h2 (∃ᵢ x hpx))
end;

// XST5_2: Two-variable version. H ⊢ (∀x y·¬P) ⇒ R → H ⊢ ¬(∃x·∃y·P) ⇒ R
opaque symbol XST5_2 [P : τ ι → τ ι → Prop] [R : Prop]
  : π ((`∀ x, `∀ y, ¬ (P x y)) ⇒ R)
  → π (¬ (`∃ x, `∃ y, P x y) ⇒ R) ≔
begin
  assume P R h1 h2;
  refine h1 (λ x y hpxy, h2 (∃ᵢ x (∃ᵢ y hpxy)))
end;

// XST51: H ⊢ (∀x·P) ⇒ R → H ⊢ ¬(∃x·¬P) ⇒ R
opaque symbol XST51 [P : τ ι → Prop] [R : Prop]
  : π ((`∀ x, P x) ⇒ R)
  → π (¬ (`∃ x, ¬ (P x)) ⇒ R) ≔
begin
  assume P R h1 h2;
  refine h1 (λ x, ¬¬ₑ (P x) (λ hnpx, h2 (∃ᵢ x hnpx)))
end;

// XST6: H ⊢ ∀x·¬P → H ⊢ ¬(∃x·P)
opaque symbol XST6 [P : τ ι → Prop]
  : π (`∀ x, ¬ (P x))
  → π (¬ (`∃ x, P x)) ≔
begin
  assume P h1 h2;
  refine ∃ₑ h2 (λ x hpx, h1 x hpx)
end;

// XST61: H ⊢ ∀x·P → H ⊢ ¬(∃x·¬P)
// XST6_2: Two-variable version.
opaque symbol XST6_2 [P : τ ι → τ ι → Prop]
  : π (`∀ x, `∀ y, ¬ (P x y))
  → π (¬ (`∃ x, `∃ y, P x y)) ≔
begin
  assume P h1 h2;
  refine ∃ₑ h2 (λ x hx, ∃ₑ hx (λ y hpxy, h1 x y hpxy))
end;

opaque symbol XST61 [P : τ ι → Prop]
  : π (`∀ x, P x)
  → π (¬ (`∃ x, ¬ (P x))) ≔
begin
  assume P h1 h2;
  refine ∃ₑ h2 (λ x hnpx, hnpx (h1 x))
end;

// XST7: x not free in R; H ⊢ ∀x·(P ⇒ R) → H ⊢ (∃x·P) ⇒ R
// "x not free in R" means R : Prop (not τ ι → Prop).
opaque symbol XST7 [P : τ ι → Prop] [R : Prop]
  : π (`∀ x, P x ⇒ R)
  → π ((`∃ x, P x) ⇒ R) ≔
begin
  assume P R h1 h2;
  refine ∃ₑ h2 h1
end;

// XST8: x not free in H; (H ⊢ ¬P) ⇝ R; H ⊢ (∀x·R) ⇒ FALSE → H ⊢ ∃x·P
// First premise: ¬P(x) = R(x) for all x (equality-based normalisation result).
// Second premise: (∀x R(x)) ⇒ ⊥.
opaque symbol XST8 [P : τ ι → Prop] (R : τ ι → Prop)
  : π (`∀ x, ¬ (P x) = R x)
  → π ((`∀ x, R x) ⇒ ⊥)
  → π (`∃ x, P x) ≔
begin
  assume P R h1 h2;
  refine ¬¬ₑ (`∃ x, P x) _;
  assume hne;
  refine h2 (λ x, =⇒ (h1 x) (λ hpx, hne (∃ᵢ x hpx)))
end;

// XST8_2: Two-variable version for compound ∃(x,y).
opaque symbol XST8_2 [P : τ ι → τ ι → Prop] (R : τ ι → τ ι → Prop)
  : π (`∀ x, `∀ y, ¬ (P x y) = R x y)
  → π ((`∀ x, `∀ y, R x y) ⇒ ⊥)
  → π (`∃ x, `∃ y, P x y) ≔
begin
  assume P R h1 h2;
  refine ¬¬ₑ (`∃ x, `∃ y, P x y) _;
  assume hne;
  refine h2 (λ x y, =⇒ (h1 x y) (λ hpxy, hne (∃ᵢ x (∃ᵢ y hpxy))))
end;

// ---- Primed variants (equality-based) ----

// XST7_1: pass-through. (∃x.P(x))⇒R = (∀x.P(x)⇒R).
opaque symbol XST7_1 [P : τ ι → Prop] [R : Prop] [S : Prop]
  : π (((`∀ x, P x ⇒ R)) = S)
  → π (((`∃ x, P x) ⇒ R) = S) ≔
begin
  assume P R S h;
  have eq : π (((`∃ x, P x) ⇒ R) = (`∀ x, P x ⇒ R))
    { refine propExt _ _ _ _
      { assume h1 x hpx; refine h1 (∃ᵢ x hpx) }
      { assume h1 hex; refine ∃ₑ hex h1 } };
  rewrite eq; refine h
end;
