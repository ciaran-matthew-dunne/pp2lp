// Axiom rules (§A.6) — shallow encoding
require open pp2lp.B pp2lp.Quant pp2lp.rules.Conj pp2lp.rules.Res;

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

// AXM9: ∀-block·¬(TRUE ∧ P) in H; v is an instantiation tuple
//       → H ⊢ P v ⇒ Q
// With HOAS the substitution is implicit: instantiating the universal
// at v reduces ¬(⊤ ∧ P v) to ¬P v, so P v ⇒ Q is trivially true.
// Tuple-uniform: replaces AXM9 (unary) and AXM9_2 (per-arity copy).

opaque symbol AXM9 [n] [P : Tuple n → Prop] (v : Tuple n) [Q]
  : π (`!! u, ¬ ⋀ (∎ ∷ ⊤ ∷ P u))
  → π (P v ⇒ Q) ≔
begin
  assume n P v Q h hp;
  refine ⊥ₑ (!!_to_pi (λ u, ¬ ⋀ (∎ ∷ ⊤ ∷ P u)) h v (⋀₂_intro ⊤ᵢ hp))
end;

// ---- `_1` (Result-form) variants — §8.13 ----
//
// All AXM rules are Schema 0 (no genuine antecedent — the hyp lookup
// is a side-condition). Per spec the result is TRUE. The proofs of
// `(rule_consequent = ⊤)` rely on PP's having confirmed the rule's
// applicability and are passed as `trust` since the chain emit does
// not thread the hyp arg.

// AXM7_1: the only AXM_N_1 whose proof is unconditional — `P ⇒ P` is
// always propositionally `⊤` (stdlib `⇒_idem`).
symbol AXM7_1 [P : Prop] : Res (P ⇒ P) ≔ mk_1 ⊤ (⇒_idem P);

symbol AXM1_1 [P Q : Prop] : Res (P ⇒ Q) ≔ mk_1 ⊤ trust;
symbol AXM2_1 [P Q : Prop] : Res (¬ P ⇒ Q) ≔ mk_1 ⊤ trust;
symbol AXM3_1 [P : Prop] : Res P ≔ mk_1 ⊤ trust;
symbol AXM4_1 [P R : Prop] : Res (P ⇒ R) ≔ mk_1 ⊤ trust;
symbol AXM5_1 [P Q R : Prop] : Res (P ⇒ (Q ⇒ R)) ≔ mk_1 ⊤ trust;
symbol AXM6_1 [P Q R : Prop] : Res (P ⇒ (¬ Q ⇒ R)) ≔ mk_1 ⊤ trust;
symbol AXM8_1 [C r : Prop] : Res (C ⇒ r) ≔ mk_1 ⊤ trust;
symbol AXM9_1 [n] [P : Tuple n → Prop] [Q : Prop]
  : Res (P (@inh_tuple n) ⇒ Q)
  ≔ mk_1 ⊤ trust;

