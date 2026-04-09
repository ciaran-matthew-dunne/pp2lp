// Normalisation (§A.12) — shallow encoding
//
// With HOAS and ♢/♡ defined as ∀ in B.lp:
// - Compound variables (⨾) become nested ∀
// - Substitution is HOAS application
// - Non-freeness is implicit (Prop vs τ ι → Prop)
require open pp2lp.B;

// ---- NRM1-7: Logical transformations under ♢ ----

// NRM1: x not free in P; H ⊢ P ⇒ S → H ⊢ (♢x · P) ⇒ S
opaque symbol NRM1 [P S : Prop]
  : π (P ⇒ S)
  → π ((`♢ _ : τ ι, P) ⇒ S) ≔
begin
  assume P S h1 h2;
  refine h1 (h2 inh)
end;

// NRM2: x not free in P; H ⊢ (P ⇒ ♢x · Q) ⇒ S → H ⊢ ♢x · (P ⇒ Q) ⇒ S
opaque symbol NRM2 [P : Prop] [Q : τ ι → Prop] [S : Prop]
  : π ((P ⇒ (`♢ x, Q x)) ⇒ S)
  → π ((`♢ x, P ⇒ Q x) ⇒ S) ≔
begin
  assume P Q S h1 h2;
  refine h1 (λ hp x, h2 x hp)
end;

// NRM3: x not free in Q; Q is not FALSE; H ⊢ (Q ⇒ S) ∧ ((∀x · ¬P) ⇒ S) → H ⊢ ♢x · (P ⇒ Q) ⇒ S
opaque symbol NRM3 [P : τ ι → Prop] [Q S : Prop]
  : π ((Q ⇒ S) ∧ ((`∀ x, ¬ (P x)) ⇒ S))
  → π ((`♢ x, P x ⇒ Q) ⇒ S) ≔
begin
  assume P Q S h1 h2;
  refine ∨ₑ (em (`∃ x, P x)) _ _ {
    assume hex;
    refine ∃ₑ hex (λ x hpx, (∧ₑ₁ h1) (h2 x hpx))
  } {
    assume hnex;
    refine (∧ₑ₂ h1) (λ x hpx, hnex (∃ᵢ x hpx))
  }
end;

opaque symbol NRM4 [P R : τ ι → Prop] [Q S : Prop]
  : π ((Q ⇒ (`♢ x, P x ⇒ R x)) ⇒ S)
  → π ((`♢ x, P x ⇒ Q ⇒ R x) ⇒ S) ≔
begin
  assume P R Q S h1 h2;
  refine h1 (λ hq x hpx, h2 x hpx hq)
end;

opaque symbol NRM5 [P Q R : τ ι → Prop] [S : Prop]
  : π ((`♢ x, P x ∧ Q x ⇒ R x) ⇒ S)
  → π ((`♢ x, P x ⇒ Q x ⇒ R x) ⇒ S) ≔
begin
  assume P Q R S h1 h2;
  refine h1 (λ x hpq, h2 x (∧ₑ₁ hpq) (∧ₑ₂ hpq))
end;

// NRM5_2: Two-variable version.
opaque symbol NRM5_2 [P Q R : τ ι → τ ι → Prop] [S : Prop]
  : π ((`♢ x, `♢ y, P x y ∧ Q x y ⇒ R x y) ⇒ S)
  → π ((`♢ x, `♢ y, P x y ⇒ Q x y ⇒ R x y) ⇒ S) ≔
begin
  assume P Q R S h1 h2;
  refine h1 (λ x y hpq, h2 x y (∧ₑ₁ hpq) (∧ₑ₂ hpq))
end;

// NRM6: H ⊢ ♢x · (R ⇒ P) ⇒ (♢x · (R ⇒ Q) ⇒ S) → H ⊢ ♢x · (R ⇒ P ∧ Q) ⇒ S
opaque symbol NRM6 [P Q R : τ ι → Prop] [S : Prop]
  : π ((`♢ x, R x ⇒ P x) ⇒ ((`♢ x, R x ⇒ Q x) ⇒ S))
  → π ((`♢ x, R x ⇒ P x ∧ Q x) ⇒ S) ≔
begin
  assume P Q R S h1 h2;
  refine h1 (λ x hr, ∧ₑ₁ (h2 x hr)) (λ x hr, ∧ₑ₂ (h2 x hr))
end;

// NRM7: H ⊢ (♢x · P) ⇒ ((♢x · Q) ⇒ S) → H ⊢ ♢x · (P ∧ Q) ⇒ S
opaque symbol NRM7 [P Q : τ ι → Prop] [S : Prop]
  : π ((`♢ x, P x) ⇒ ((`♢ x, Q x) ⇒ S))
  → π ((`♢ x, P x ∧ Q x) ⇒ S) ≔
begin
  assume P Q S h1 h2;
  refine h1 (λ x, ∧ₑ₁ (h2 x)) (λ x, ∧ₑ₂ (h2 x))
end;

// NRM7_2: Two-variable version.
opaque symbol NRM7_2 [P Q : τ ι → τ ι → Prop] [S : Prop]
  : π ((`♢ x, `♢ y, P x y) ⇒ ((`♢ x, `♢ y, Q x y) ⇒ S))
  → π ((`♢ x, `♢ y, P x y ∧ Q x y) ⇒ S) ≔
begin
  assume P Q S h1 h2;
  refine h1 (λ x y, ∧ₑ₁ (h2 x y)) (λ x y, ∧ₑ₂ (h2 x y))
end;

opaque symbol NRM8 [Q : τ ι → τ ι → Prop] [S : Prop]
  : π ((`♢ x, `♢ y, Q x y) ⇒ S)
  → π ((`♢ x, `∀ y, Q x y) ⇒ S) ≔
begin
  assume Q S h; refine h
end;

opaque symbol NRM9 [P : τ ι → Prop] [Q : τ ι → τ ι → Prop] [S : Prop]
  : π ((`♢ x, `♢ y, P x ⇒ Q x y) ⇒ S)
  → π ((`♢ x, P x ⇒ `∀ y, Q x y) ⇒ S) ≔
begin
  assume P Q S h1 h2;
  refine h1 (λ x y hp, h2 x hp y)
end;

opaque symbol NRM10 [P Q : τ ι → Prop] [R : Prop]
  : π ((`♡ x, ¬ (P x ∧ Q x)) ⇒ R)
  → π ((`♢ x, (P x ∧ Q x) ⇒ ⊥) ⇒ R) ≔
begin
  admit;
end;

opaque symbol NRM11 [P : τ ι → Prop] [R : Prop]
  : π ((`♡ x, ¬ (⊤ ∧ P x)) ⇒ R)
  → π ((`♢ x, P x ⇒ ⊥) ⇒ R) ≔
begin
  admit;
end;

opaque symbol NRM12 [P Q : τ ι → Prop] [R : Prop]
  : π ((`♡ x, ¬ (P x ∧ Q x)) ⇒ R)
  → π ((`♢ x, P x ⇒ ¬ (Q x)) ⇒ R) ≔
begin
  assume P Q R h1 h2;
  refine h1 (λ x hpq, h2 x (∧ₑ₁ hpq) (∧ₑ₂ hpq))
end;

opaque symbol NRM13 [P Q : τ ι → Prop] [R : Prop]
  : π ((`♡ x, ¬ (P x ∧ ¬ (Q x))) ⇒ R)
  → π ((`♢ x, P x ⇒ Q x) ⇒ R) ≔
begin
  assume P Q R h1 h2;
  refine h1 (λ x hc, (∧ₑ₂ hc) (h2 x (∧ₑ₁ hc)))
end;

// NRM13_2: Two-variable version.
opaque symbol NRM13_2 [P Q : τ ι → τ ι → Prop] [R : Prop]
  : π ((`♡ x, `♡ y, ¬ (P x y ∧ ¬ (Q x y))) ⇒ R)
  → π ((`♢ x, `♢ y, P x y ⇒ Q x y) ⇒ R) ≔
begin
  assume P Q R h1 h2;
  refine h1 (λ x y hpnq, (∧ₑ₂ hpnq) (h2 x y (∧ₑ₁ hpnq)))
end;

opaque symbol NRM14 [P : τ ι → Prop] [R : Prop]
  : π ((`♡ x, ¬ (⊤ ∧ P x)) ⇒ R)
  → π ((`♢ x, ¬ P x) ⇒ R) ≔
begin
  assume P R h1 h2;
  refine h1 (λ x htpx, h2 x (∧ₑ₂ htpx))
end;

// NRM14_2: Two-variable version.
opaque symbol NRM14_2 [P : τ ι → τ ι → Prop] [R : Prop]
  : π ((`♡ x, `♡ y, ¬ (⊤ ∧ P x y)) ⇒ R)
  → π ((`♢ x, `♢ y, ¬ (P x y)) ⇒ R) ≔
begin
  assume P R h1 h2;
  refine h1 (λ x y htpxy, h2 x y (∧ₑ₂ htpxy))
end;

opaque symbol NRM15 [P : τ ι → Prop] [R : Prop]
  : π ((`♡ x, ¬ (⊤ ∧ ¬ P x)) ⇒ R)
  → π ((`♢ x, P x) ⇒ R) ≔
begin
  assume P R h1 h2;
  refine h1 (λ x htnpx, (∧ₑ₂ htnpx) (h2 x))
end;

// NRM15_2: Two-variable version.
opaque symbol NRM15_2 [P : τ ι → τ ι → Prop] [R : Prop]
  : π ((`♡ x, `♡ y, ¬ (⊤ ∧ ¬ (P x y))) ⇒ R)
  → π ((`♢ x, `♢ y, P x y) ⇒ R) ≔
begin
  assume P R h1 h2;
  refine h1 (λ x y htnpxy, (∧ₑ₂ htnpxy) (h2 x y))
end;

opaque symbol NRM16 [P : τ ι → Prop] [Q : Prop]
  : π (`∀ x, P x)
  → π Q
  → π ((`♡ x, P x) ⇒ Q) ≔
begin
  assume P Q hp hq ht; refine hq
end;

opaque symbol NRM17 [P : τ ι → Prop] [Q : Prop]
  : π (`∀ x, P x)
  → π Q
  → π ((`♡ x, P x) ⇒ Q) ≔
begin
  assume P Q hp hq ht; refine hq
end;

opaque symbol NRM18 [P : τ ι → Prop] [R Q : Prop] (E : τ ι)
  : π (`∀ x, ¬ (⊤ ∧ ¬ P x))
  → π (P E = R)
  → π ((`♡ y, ¬ (⊤ ∧ R)) ⇒ Q) ≔
begin
  admit
end;

opaque symbol NRM19 [Q : Prop] [R : τ ι → Prop] (E : τ ι)
  : π (R E)
  → π ((`♡ x, ¬ (⊤ ∧ R x)) ⇒ Q) ≔
begin
  assume Q R E hr hf;
  refine ⊥ₑ (hf E (∧ᵢ ⊤ᵢ hr))
end;

// NRM19_2: Two-variable version.
opaque symbol NRM19_2 [Q : Prop] [R : τ ι → τ ι → Prop] (E F : τ ι)
  : π (R E F)
  → π ((`♡ x, `♡ y, ¬ (⊤ ∧ R x y)) ⇒ Q) ≔
begin
  assume Q R E F hr hf;
  refine ⊥ₑ (hf E F (∧ᵢ ⊤ᵢ hr))
end;

opaque symbol NRM20 [P : τ ι → τ ι → Prop] [Q : Prop] (E : τ ι)
  : π ((`♡ y, ¬ (P E y)) ⇒ Q)
  → π ((`♡ x, `♡ y, ¬ (P x y ∧ (x = E))) ⇒ Q) ≔
begin
  assume P Q E h1 h2;
  refine h1 (λ y hpey, h2 E y (∧ᵢ hpey (eq_refl E)))
end;

opaque symbol NRM21 [P : τ ι → τ ι → Prop] [Q : Prop] (E : τ ι)
  : π ((`♡ y, ¬ (P E y)) ⇒ Q)
  → π ((`♡ x, `♡ y, ¬ (P x y ∧ (E = x))) ⇒ Q) ≔
begin
  assume P Q E h1 h2;
  refine h1 (λ y hpey, h2 E y (∧ᵢ hpey (eq_sym (eq_refl E))))
end;

opaque symbol NRM22 [P : τ ι → Prop] [Q : Prop] (E : τ ι)
  : π (¬ (P E) ⇒ Q)
  → π ((`♡ x, ¬ (P x ∧ (x = E))) ⇒ Q) ≔
begin
  assume P Q E h1 h2;
  refine h1 (λ hpe, h2 E (∧ᵢ hpe (eq_refl E)))
end;

opaque symbol NRM23 [P : τ ι → Prop] [Q : Prop] (E : τ ι)
  : π (¬ (P E) ⇒ Q)
  → π ((`♡ x, ¬ (P x ∧ (E = x))) ⇒ Q) ≔
begin
  assume P Q E h1 h2;
  refine h1 (λ hpe, h2 E (∧ᵢ hpe (eq_sym (eq_refl E))))
end;

opaque symbol NRM24 [P : τ ι → Prop] [Q : Prop]
  : π ((`♡ x, ¬ (⊤ ∧ P x)) ⇒ Q)
  → π ((`♡ x, ¬ (P x)) ⇒ Q) ≔
begin
  assume P Q h1 h2;
  refine h1 (λ x htpx, h2 x (∧ₑ₂ htpx))
end;

// NRM25: x not free in P; H ⊢ P → H ⊢ ♡(x) · P
opaque symbol NRM25 [P : Prop]
  : π P
  → π (`♡ _ : τ ι, P) ≔
begin
  assume P hp x; refine hp
end;

// NRM26: y not free in P; H ⊢ ♡(x, ...) · P → H ⊢ ♡(x, y, ...) · P
opaque symbol NRM26 [P : τ ι → Prop]
  : π (`♡ x, P x)
  → π (`♡ x, `∀ _ : τ ι, P x) ≔
begin
  assume P h x y; refine h x
end;

// ---- NRM27-30: Arithmetic solver dispatch ----
//
// NRM27: (xᵢ ≤ 0) and (−xᵢ ≤ 0) in (P ∧...∧ Q); R = [xᵢ := 0](P ∧...∧ Q)
//   → H ⊢ ♢(x₁,...,xᵢ₋₁,xᵢ₊₁,...,xₙ) · ¬R → H ⊢ ♡(x₁,...,xₙ) · ¬(P ∧...∧ Q)
// NRM28: (x ≤ 0) and (−x ≤ 0) in (P ∧...∧ Q); S = [x := 0](P ∧...∧ Q)
//   → H ⊢ ¬(S) ⇒ R → H ⊢ (♡(x) · ¬(P ∧...∧ Q)) ⇒ R
// NRM29: (a + xᵢ ≤ 0) and (b − xᵢ ≤ 0) in (P ∧...∧ Q); solver(a+b) = 0; S = [xᵢ := b](P ∧...∧ Q)
//   → H ⊢ ♢(...) · ¬S ⇒ R → H ⊢ (♡(x₁,...,xₙ) · ¬(P ∧...∧ Q)) ⇒ R
// NRM30: (a + x ≤ 0) and (b − x ≤ 0) in (P ∧...∧ Q); solver(a+b) = 0; S = [x := b](P ∧...∧ Q)
//   → H ⊢ ¬S ⇒ R → H ⊢ (♡x · ¬(P ∧...∧ Q)) ⇒ R
// TODO: all require arithmetic solver infrastructure
