// Axiom rules (§A.6) — shallow encoding
require open pp2lp.B pp2lp.rules.Conj;

// ---- Base rules ----

// AXM1: ¬P in H → H ⊢ P ⇒ Q
opaque symbol AXM1 [P Q]
  : π (¬ P)
  → π (P ⇒ Q) ≔
begin
  assume P Q h1 h2;
  refine ⊥ₑ (h1 h2)
end;

// AXM2: P in H → H ⊢ ¬P ⇒ Q
opaque symbol AXM2 [P Q]
  : π P
  → π (¬ P ⇒ Q) ≔
begin
  assume P Q h1 h2;
  refine ⊥ₑ (h2 h1)
end;

// AXM3: P in H → H ⊢ P
opaque symbol AXM3 [P]
  : π P
  → π P ≔
begin
  assume P h1;
  refine h1
end;

// AXM4: R in H → H ⊢ P ⇒ R
opaque symbol AXM4 [P R]
  : π R
  → π (P ⇒ R) ≔
begin
  assume P R h1 h2;
  refine h1
end;

// AXM5: ¬Q in H → H ⊢ P ⇒ (Q ⇒ R)
opaque symbol AXM5 [P Q R]
  : π (¬ Q)
  → π (P ⇒ (Q ⇒ R)) ≔
begin
  assume P Q R h1 h2 h3;
  refine ⊥ₑ (h1 h3)
end;

// AXM6: Q in H → H ⊢ P ⇒ (¬Q ⇒ R)
opaque symbol AXM6 [P Q R]
  : π Q
  → π (P ⇒ (¬ Q ⇒ R)) ≔
begin
  assume P Q R h1 h2 h3;
  refine ⊥ₑ (h3 h1)
end;

// AXM7: H ⊢ P ⇒ P
opaque symbol AXM7 [P]
  : π (P ⇒ P) ≔
begin
  assume P h1;
  refine h1
end;

// ---- AXM8: Conjunction membership ----

// AXM8: extract a conjunct from the antecedent.
// The caller supplies an extraction function (chain of ∧ₑ₁/∧ₑ₂).
opaque symbol AXM8 [C r : Prop]
  : (π C → π r)
  → π (C ⇒ r) ≔
begin
  assume C r f hc; refine f hc
end;

// ---- AXM9: Universal instantiation from hypothesis ----

// AXM9: ∀x·¬(TRUE ∧ P) in H; ∃E such that [x:=E]P = R → H ⊢ R ⇒ Q
// With HOAS: from ∀x.¬(⊤∧P(x)), instantiate with e to get ¬P(e),
// so P(e) ⇒ Q is trivially true.
opaque symbol AXM9 [P : τ ι → Prop] (e : τ ι) [Q]
  : π (`∀ x, ¬ (⊤ ∧ P x))
  → π (P e ⇒ Q) ≔
begin
  assume P e Q h hp;
  refine ⊥ₑ (h e (∧ᵢ ⊤ᵢ hp))
end;
// AXM9_2: Two-variable version.
opaque symbol AXM9_2 [P : τ ι → τ ι → Prop] (e1 e2 : τ ι) [Q]
  : π (`∀ x, `∀ y, ¬ (⊤ ∧ P x y))
  → π (P e1 e2 ⇒ Q) ≔
begin
  assume P e1 e2 Q h hp;
  refine ⊥ₑ (h e1 e2 (∧ᵢ ⊤ᵢ hp))
end;

