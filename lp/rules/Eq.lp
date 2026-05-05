// Equality rules (§A.13) — shallow encoding
// Exp ≃ Exp becomes Leibniz equality (polymorphic)
require open pp2lp.B pp2lp.Quant;

// ---- EVR (equality reflexivity) ----

// EVR1: H ⊢ ¬(E = E) ⇒ P
opaque symbol EVR1 [E : τ ι] [P]
  : π (¬ (E = E) ⇒ P) ≔
begin
  assume E P h;
  refine ⊥ₑ (h (eq_refl E))
end;

// EVR11: n ≠ m → H ⊢ (n = m) ⇒ P
opaque symbol EVR11 [n m : τ ι] [P]
  : π (n ϵ NAT) → π (m ϵ NAT)
  → π (n ≠ m) → π ((n = m) ⇒ P) ≔
begin
  assume n m nN mN P h1 h2;
  refine ⊥ₑ (h1 h2)
end;

// EVR2: H ⊢ ⊥ → H ⊢ ¬(E = E)
opaque symbol EVR2 [E : τ ι]
  : π ⊥
  → π (¬ (E = E)) ≔
begin
  assume E h h0; refine h
end;

// EVR3: H ⊢ P → H ⊢ (E = E) ⇒ P
opaque symbol EVR3 [E : τ ι] [P]
  : π P
  → π ((E = E) ⇒ P) ≔
begin
  assume E P h h0; refine h
end;

// EVR4: H ⊢ E = E
opaque symbol EVR4 [E : τ ι]
  : π (E = E) ≔
begin
  assume E; reflexivity
end;

// ---- EAXM (equality axioms due to commutativity) ----

// EAXM1: ¬(F = E) in H → H ⊢ (E = F) ⇒ P
opaque symbol EAXM1 [E F : τ ι] [P]
  : π (¬ (F = E))
  → π ((E = F) ⇒ P) ≔
begin
  assume E F P h1 h2;
  refine ⊥ₑ (h1 (eq_sym h2))
end;

// EAXM2: (F = E) in H → H ⊢ ¬(E = F) ⇒ P
opaque symbol EAXM2 [E F : τ ι] [P]
  : π (F = E)
  → π (¬ (E = F) ⇒ P) ≔
begin
  assume E F P h1 h2;
  refine ⊥ₑ (h2 (eq_sym h1))
end;

// EAXM31: (F = E) in H → H ⊢ E = F
opaque symbol EAXM31 [E F : τ ι]
  : π (F = E)
  → π (E = F) ≔
begin
  assume E F h; refine eq_sym h
end;

// EAXM32: ¬(F = E) in H → H ⊢ ¬(E = F)
opaque symbol EAXM32 [E F : τ ι]
  : π (¬ (F = E))
  → π (¬ (E = F)) ≔
begin
  assume E F h1 h2;
  refine h1 (eq_sym h2)
end;

// EIMP51: ¬(F = E) in H; H ⊢ P → H ⊢ ¬(E = F) ⇒ P
opaque symbol EIMP51 [E F : τ ι] [P]
  : π (¬ (F = E))
  → π P
  → π (¬ (E = F) ⇒ P) ≔
begin
  assume E F P h1 h2 h3; refine h2
end;

// EIMP52: (F = E) in H; H ⊢ P → H ⊢ (E = F) ⇒ P
opaque symbol EIMP52 [E F : τ ι] [P]
  : π (F = E)
  → π P
  → π ((E = F) ⇒ P) ≔
begin
  assume E F P h1 h2 h3; refine h2
end;

// ---- EAXM91/EAXM92: AXM9 extensions for equality commutativity ----
//
// Tuple-uniform like AXM9. The hypothesis pattern is the same
// `!! u, ¬(⊤ ∧ …)` shape; EAXM91/92 only differ from AXM9 in
// applying eq commutativity at the conclusion.

// EAXM91: !!-block ¬(⊤ ∧ p=q) in H; v is an instantiation tuple
//         → H ⊢ (q v = p v) ⇒ Q
opaque symbol EAXM91 [n] [p q : Tuple n → τ ι] (v : Tuple n) [Q]
  : π (`!! u, ¬ (⊤ ∧ (p u = q u)))
  → π ((q v = p v) ⇒ Q) ≔
begin
  assume n p q v Q hall h;
  refine ⊥ₑ (!!_to_pi (λ u, ¬ (⊤ ∧ (p u = q u))) hall v
              (∧ᵢ ⊤ᵢ (eq_sym h)))
end;

// EAXM92: !!-block ¬(⊤ ∧ ¬(p=q)) in H; v is an instantiation tuple
//         → H ⊢ ¬(q v = p v) ⇒ Q
opaque symbol EAXM92 [n] [p q : Tuple n → τ ι] (v : Tuple n) [Q]
  : π (`!! u, ¬ (⊤ ∧ ¬ (p u = q u)))
  → π (¬ (q v = p v) ⇒ Q) ≔
begin
  assume n p q v Q hall h;
  refine ⊥ₑ (h (eq_sym _));
  refine ¬¬ₑ (p v = q v) _;
  assume hnpq;
  refine !!_to_pi (λ u, ¬ (⊤ ∧ ¬ (p u = q u))) hall v
         (∧ᵢ ⊤ᵢ hnpq)
end;

// ---- OPR (one-point rules / substitution from equality) ----

opaque symbol OPR1 [E x : τ ι] (P : τ ι → Prop)
  : π (P E)
  → π ((x = E) ⇒ P x) ≔
begin
  assume E x P hpe heq;
  rewrite heq; refine hpe
end;

opaque symbol OPR2 [E x : τ ι] (P : τ ι → Prop)
  : π (P E)
  → π ((E = x) ⇒ P x) ≔
begin
  assume E x P hpe heq;
  rewrite left heq; refine hpe
end;

// ---- EQC (pair equality decomposition) ----

// EQC1: H ⊢ (¬(a=c) ∨ ¬(b=d)) ⇒ P → H ⊢ ¬((a↦b)=(c↦d)) ⇒ P
opaque symbol EQC1 [a b c d : τ ι] [P]
  : π ((¬ (a = c) ∨ ¬ (b = d)) ⇒ P)
  → π (¬ ((a ↦ b) = (c ↦ d)) ⇒ P) ≔
begin
  assume a b c d P h1 h2;
  refine h1 _;
  refine ∨ₑ (em (a = c)) _ _
  { assume hac; refine ∨ₑ (em (b = d)) _ _
    { assume hbd;
      refine ⊥ₑ (h2 (pair_cong a b c d hac hbd)) }
    { assume hnbd; refine ∨ᵢ₂ hnbd } }
  { assume hnac; refine ∨ᵢ₁ hnac }
end;

// EQC2: H ⊢ (a=c) ∧ (b=d) ⇒ P → H ⊢ ((a↦b)=(c↦d)) ⇒ P
opaque symbol EQC2 [a b c d : τ ι] [P]
  : π (((a = c) ∧ (b = d)) ⇒ P)
  → π (((a ↦ b) = (c ↦ d)) ⇒ P) ≔
begin
  assume a b c d P h1 h2;
  refine h1 (pair_inj a b c d h2)
end;

// ---- EQS (set equality) ----
// eql_set(E,F) is modeled as ∀x.(x∈E ⇔ x∈F) (set extensionality).

symbol eql_set (X Y : τ ι) ≔
  (`∀ a, (a ϵ X) ⇔ (a ϵ Y));

// EQS1: H ⊢ (E=F) ⇒ R → H ⊢ eql_set(E,F) ⇒ R
// From (E=F)⇒R, derive (∀x.x∈E⇔x∈F)⇒R.
opaque symbol EQS1 [E F : τ ι] [R]
  : π ((E = F) ⇒ R)
  → π (eql_set E F ⇒ R) ≔
begin
  assume E F R h1 h2;
  refine h1 (∧ₑ₂ (set_ext E F) h2)
end;


// EQS2: H ⊢ ¬ (E = F) ⇒ R → H ⊢ ¬eql_set(E,F) ⇒ R
// NOTE: spec incorrectly has (H ⊢ FAUX ⇒ R) as antecedent.
opaque symbol EQS2 [E F : τ ι] [R]
  : π (¬ (E = F) ⇒ R)
  → π (¬ eql_set E F ⇒ R) ≔
begin
  assume E F R h1 h2;
  refine h1 (λ heq, ⊥ₑ (h2 (∧ₑ₁ (set_ext E F) heq)))
end;

// ---- ECTR (contradiction due to equalities) ----
// These rules use substitution: "replacing E by F in Q gives R"
// means R = [E→F]Q. In HOAS, Q(E) is the original, Q(F) is the
// result of replacement. The parameter Q : τ ι → Prop is the
// predicate with E abstracted out.

// ECTR1: ¬Q in H; [E→F]Q = R in H → H ⊢ (E=F) ⇒ P
// ¬Q(E) and Q(F) in H. If E=F then Q(E)=Q(F), contradiction.
opaque symbol ECTR1 [E F : τ ι] (Q : τ ι → Prop) [P]
  : π (¬ (Q E))
  → π (Q F)
  → π ((E = F) ⇒ P) ≔
begin
  assume E F Q P hnq hr heq;
  have hqe : π (Q E) { rewrite heq; refine hr };
  refine ⊥ₑ (hnq hqe)
end;

// ECTR2: ¬Q in H; [E→F]Q = R in H → H ⊢ (F=E) ⇒ P
opaque symbol ECTR2 [E F : τ ι] (Q : τ ι → Prop) [P]
  : π (¬ (Q E))
  → π (Q F)
  → π ((F = E) ⇒ P) ≔
begin
  assume E F Q P hnq hr heq;
  have hqe : π (Q E) { rewrite left heq; refine hr };
  refine ⊥ₑ (hnq hqe)
end;

// ECTR3: (E=F) in H; [E→F]P = R in H → H ⊢ ¬P ⇒ Q
// E=F known, P(F) in H. If ¬P(E), but E=F ⇒ P(E)=P(F), contradiction.
opaque symbol ECTR3 [E F : τ ι] (P : τ ι → Prop) [Q]
  : π (E = F)
  → π (P F)
  → π (¬ (P E) ⇒ Q) ≔
begin
  assume E F P Q heq hr hnp;
  have hpe : π (P E) { rewrite heq; refine hr };
  refine ⊥ₑ (hnp hpe)
end;

// ECTR4: (F=E) in H; [E→F]P = R in H → H ⊢ ¬P ⇒ Q
opaque symbol ECTR4 [E F : τ ι] (P : τ ι → Prop) [Q]
  : π (F = E)
  → π (P F)
  → π (¬ (P E) ⇒ Q) ≔
begin
  assume E F P Q heq hr hnp;
  have hpe : π (P E) { rewrite left heq; refine hr };
  refine ⊥ₑ (hnp hpe)
end;

// ECTR5: (E=F) in H; [E→F]P = R; ¬R in H → H ⊢ P ⇒ Q
// E=F known, ¬P(F) in H. If P(E), then P(F) by E=F, contradiction.
opaque symbol ECTR5 [E F : τ ι] (P : τ ι → Prop) [Q]
  : π (E = F)
  → π (¬ (P F))
  → π ((P E) ⇒ Q) ≔
begin
  assume E F P Q heq hnr hp;
  have hpf : π (P F) { rewrite (eq_sym heq); refine hp };
  refine ⊥ₑ (hnr hpf)
end;

// ECTR6: (F=E) in H; [E→F]P = R; ¬R in H → H ⊢ P ⇒ Q
opaque symbol ECTR6 [E F : τ ι] (P : τ ι → Prop) [Q]
  : π (F = E)
  → π (¬ (P F))
  → π ((P E) ⇒ Q) ≔
begin
  assume E F P Q heq hnr hp;
  have hpf : π (P F) { rewrite heq; refine hp };
  refine ⊥ₑ (hnr hpf)
end;
