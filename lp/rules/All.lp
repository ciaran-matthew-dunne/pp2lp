// Universal quantification (§A.7) — shallow encoding
//
// With HOAS:
// - ♢ and ♡ are defined as aliases for ∀ in B.lp.
// - Variable renaming (ALL5f, ALL7f, ALL8f) is handled by
//   α-equivalence — these collapse into ALL5, ALL7, ALL8.
// - Compound variables (ALL1-4) don't exist; nested ∀ IS
//   the only form. The OCaml emitter should skip ALL1-4.
// - ALL6 is definitional (¬Q ≡ Q ⇒ ⊥).
require open pp2lp.B;

// ---- Identity rules (no-ops in HOAS) ----
//
// ALL5f, ALL7f, ALL8f: Variable renaming variants of ALL5,
//   ALL7, ALL8. In HOAS, α-equivalence is automatic, so
//   these collapse into their base forms.

// ALL1-4: Compound variable flattening (identity in HOAS).
// ALL1: x,y distinct; H ⊢ ¬(∀(x,y)·P) ⇒ R → H ⊢ ¬(∀x·∀y·P) ⇒ R
opaque symbol ALL1 [P : τ ι → τ ι → Prop] [R : Prop] (nf : π ⊤)
  : π (¬ (`∀ x, `∀ y, P x y) ⇒ R)
  → π (¬ (`∀ x, `∀ y, P x y) ⇒ R) ≔
begin assume P R nf h; refine h end;

// ALL2: same pattern for NOT(∀) flattening
opaque symbol ALL2 [P : τ ι → τ ι → Prop] (nf : π ⊤)
  : π (¬ (`∀ x, `∀ y, P x y))
  → π (¬ (`∀ x, `∀ y, P x y)) ≔
begin assume P nf h; refine h end;

// ALL3: compound variable flattening for positive ∀ ⇒ R
opaque symbol ALL3 [P : τ ι → τ ι → Prop] [R : Prop] (nf : π ⊤)
  : π ((`∀ x, `∀ y, P x y) ⇒ R)
  → π ((`∀ x, `∀ y, P x y) ⇒ R) ≔
begin assume P R nf h; refine h end;

// ALL4: flattening for ∀ with implication
opaque symbol ALL4 [P : τ ι → τ ι → Prop] [Q : Prop] (nf : π ⊤)
  : π ((`∀ x, `∀ y, P x y) ⇒ Q)
  → π ((`∀ x, `∀ y, P x y) ⇒ Q) ≔
begin assume P Q nf h; refine h end;

// ALL6: H ⊢ (∀x·P) ⇒ FALSE → H ⊢ ¬(∀x·P)
// Definitional: ¬Q ≡ Q ⇒ ⊥.
opaque symbol ALL6 [P : τ ι → Prop]
  : π ((`∀ x, P x) ⇒ ⊥)
  → π (¬ (`∀ x, P x)) ≔
begin assume P h; refine h end;

// ---- Substantive rules ----

// ALL5: x not free in R; H ⊢ ∀x·(¬P ⇒ R) → H ⊢ ¬(∀x·P) ⇒ R
// "x not free in R" means R : Prop (not τ ι → Prop).
opaque symbol ALL5 [P : τ ι → Prop] [R : Prop]
  : π (`∀ x, ¬ (P x) ⇒ R)
  → π (¬ (`∀ x, P x) ⇒ R) ≔
begin
  assume P R h1 h2;
  refine ¬¬ₑ R _;
  assume hnr;
  refine h2 (λ x, ¬¬ₑ (P x) (λ hnpx, hnr (h1 x hnpx)))
end;

// ALL7: x not free in H; (H ⊢ P) ⇝ R; H ⊢ (♢x·R) ⇒ Q → H ⊢ (∀x·P) ⇒ Q
// First premise: P(x) = R(x) for all x (equality-based normalisation result).
// Second premise: (♢x R(x)) ⇒ Q.
opaque symbol ALL7 [P : τ ι → Prop] (R : τ ι → Prop) [Q : Prop]
  : π (`∀ x, P x = R x)
  → π ((`♢ x, R x) ⇒ Q)
  → π ((`∀ x, P x) ⇒ Q) ≔
begin
  assume P R Q h1 h2 hP;
  refine h2 (λ x, =⇒ (h1 x) (hP x))
end;

// ALL7_2: Two-variable version for compound ∀(x,y).
opaque symbol ALL7_2 [P : τ ι → τ ι → Prop] (R : τ ι → τ ι → Prop) [Q : Prop]
  : π (`∀ x, `∀ y, P x y = R x y)
  → π ((`♢ x, `♢ y, R x y) ⇒ Q)
  → π ((`∀ x, `∀ y, P x y) ⇒ Q) ≔
begin
  assume P R Q h1 h2 hP;
  refine h2 (λ x y, =⇒ (h1 x y) (hP x y))
end;

// ALL8: x not free in H; H ⊢ P → H ⊢ ∀x·P
// Identity in HOAS: π(∀x, P x) is already Πx, π(P x).
// The emitter handles ∀-introduction via assume.
opaque symbol ALL8 [P : τ ι → Prop]
  : π (`∀ x, P x)
  → π (`∀ x, P x) ≔
begin
  assume P h; refine h
end;

// ALL9: H, (∀x·T) ⊢ Q → H ⊢ (♡x·T) ⇒ Q
opaque symbol ALL9 [T : τ ι → Prop] [Q : Prop]
  : (π (`∀ x, T x) → π Q)
  → π ((`♡ x, T x) ⇒ Q) ≔
begin
  assume T Q h; refine h
end;
