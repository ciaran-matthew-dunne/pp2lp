// Equality rules (§A.13) — shallow encoding
// Exp ≃ Exp becomes Leibniz equality (polymorphic)
require open pp2lp.B;

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

// EAXM91: ∀x·¬(TRUE ∧ p=q) in H; [x:=E](q=p) reduces to (a=b) → H ⊢ (a=b) ⇒ Q
// ∀x.¬(⊤∧(p(x)=q(x))) instantiated with E gives ¬(⊤∧(p(E)=q(E))),
// i.e. p(E)≠q(E). With commutativity, (q(E)=p(E))⇒Q is trivially true.
opaque symbol EAXM91 [p q : τ ι → τ ι] (E : τ ι) [Q]
  : π (`∀ x, ¬ (⊤ ∧ (p x = q x)))
  → π ((q E = p E) ⇒ Q) ≔
begin
  assume p q E Q hall h;
  refine ⊥ₑ (hall E (∧ᵢ ⊤ᵢ (eq_sym h)))
end;

// EAXM92: ∀x·¬(TRUE ∧ ¬(p=q)) in H; [x:=E](q=p) reduces to (a=b) → H ⊢ ¬(a=b) ⇒ Q
// ∀x.¬(⊤∧¬(p(x)=q(x))) instantiated with E gives ¬(⊤∧¬(p(E)=q(E))),
// i.e. p(E)=q(E). With commutativity, ¬(q(E)=p(E))⇒Q is trivially true.
opaque symbol EAXM92 [p q : τ ι → τ ι] (E : τ ι) [Q]
  : π (`∀ x, ¬ (⊤ ∧ ¬ (p x = q x)))
  → π (¬ (q E = p E) ⇒ Q) ≔
begin
  assume p q E Q hall h;
  refine ⊥ₑ (h (eq_sym _));
  refine ¬¬ₑ (p E = q E) _;
  assume hnpq;
  refine hall E (∧ᵢ ⊤ᵢ hnpq)
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

// ---- Primed variants (equality-based) ----

// EVR1_1: leaf. ¬(E=E)⇒P = ⊤.
opaque symbol EVR1_1 [E : τ ι] [P]
  : π ((¬ (E = E) ⇒ P) = ⊤) ≔
begin
  assume E P;
  refine propExt _ _ _ _
  { assume h0; refine ⊤ᵢ }
  { assume h0 h1; refine ⊥ₑ (h1 (eq_refl E)) }
end;

// EVR11_1: leaf. (n=m)⇒P = ⊤ when n≠m.
opaque symbol EVR11_1 [n m : τ ι] [P]
  : π (n ≠ m)
  → π (((n = m) ⇒ P) = ⊤) ≔
begin
  assume n m P hneq;
  refine propExt _ _ _ _
  { assume h0; refine ⊤ᵢ }
  { assume h0 h1; refine ⊥ₑ (hneq h1) }
end;

// EVR2_1: pass-through. ¬(E=E) = ⊥.
opaque symbol EVR2_1 [E : τ ι] [S : Prop]
  : π (⊥ = S)
  → π (¬ (E = E) = S) ≔
begin
  assume E S h;
  rewrite ¬=_idem; refine h
end;

// EVR3_1: pass-through. (E=E)⇒P = P.
opaque symbol EVR3_1 [E : τ ι] [P S : Prop]
  : π (P = S)
  → π (((E = E) ⇒ P) = S) ≔
begin
  assume E P S h;
  have eq : π (((E = E) ⇒ P) = P)
    { refine propExt _ _ _ _
      { assume h1; refine h1 (eq_refl E) }
      { assume h1 h2; refine h1 } };
  rewrite eq; refine h
end;

// EVR4_1: leaf. (E=E) = ⊤.
opaque symbol EVR4_1 [E : τ ι]
  : π ((E = E) = ⊤) ≔
begin
  assume E;
  refine propExt _ _ _ _
  { assume h0; refine ⊤ᵢ }
  { assume h0; reflexivity }
end;

// EAXM1_1: leaf.
opaque symbol EAXM1_1 [E F : τ ι] [P]
  : π (¬ (F = E))
  → π (((E = F) ⇒ P) = ⊤) ≔
begin
  assume E F P h;
  refine propExt _ _ _ _
  { assume h0; refine ⊤ᵢ }
  { assume h0 h1; refine ⊥ₑ (h (eq_sym h1)) }
end;

// EAXM2_1: leaf.
opaque symbol EAXM2_1 [E F : τ ι] [P]
  : π (F = E)
  → π ((¬ (E = F) ⇒ P) = ⊤) ≔
begin
  assume E F P h;
  refine propExt _ _ _ _
  { assume h0; refine ⊤ᵢ }
  { assume h0 h1; refine ⊥ₑ (h1 (eq_sym h)) }
end;

// EAXM31_1: leaf.
opaque symbol EAXM31_1 [E F : τ ι]
  : π (F = E)
  → π ((E = F) = ⊤) ≔
begin
  assume E F h;
  refine propExt _ _ _ _
  { assume h0; refine ⊤ᵢ }
  { assume h0; refine eq_sym h }
end;

// EAXM32_1: leaf.
opaque symbol EAXM32_1 [E F : τ ι]
  : π (¬ (F = E))
  → π ((¬ (E = F)) = ⊤) ≔
begin
  assume E F h;
  refine propExt _ _ _ _
  { assume h0; refine ⊤ᵢ }
  { assume h0 h1; refine h (eq_sym h1) }
end;

// EIMP51_1: pass-through.
opaque symbol EIMP51_1 [E F : τ ι] [P S : Prop]
  : π (¬ (F = E))
  → π (P = S)
  → π ((¬ (E = F) ⇒ P) = S) ≔
begin
  assume E F P S hneq h;
  have eq : π ((¬ (E = F) ⇒ P) = P)
    { refine propExt _ _ _ _
      { assume h1; refine h1 (λ h2, hneq (eq_sym h2)) }
      { assume h1 h2; refine h1 } };
  rewrite eq; refine h
end;

// EIMP52_1: pass-through.
opaque symbol EIMP52_1 [E F : τ ι] [P S : Prop]
  : π (F = E)
  → π (P = S)
  → π (((E = F) ⇒ P) = S) ≔
begin
  assume E F P S heq h;
  have eq : π (((E = F) ⇒ P) = P)
    { refine propExt _ _ _ _
      { assume h1; refine h1 (eq_sym heq) }
      { assume h1 h2; refine h1 } };
  rewrite eq; refine h
end;

// EAXM91_1: leaf.
opaque symbol EAXM91_1 [p q : τ ι → τ ι] (E : τ ι) [Q]
  : π (`∀ x, ¬ (⊤ ∧ (p x = q x)))
  → π (((q E = p E) ⇒ Q) = ⊤) ≔
begin
  assume p q E Q hall;
  refine propExt _ _ _ _
  { assume h0; refine ⊤ᵢ }
  { assume h0 h1; refine ⊥ₑ (hall E (∧ᵢ ⊤ᵢ (eq_sym h1))) }
end;

// EAXM92_1: leaf.
opaque symbol EAXM92_1 [p q : τ ι → τ ι] (E : τ ι) [Q]
  : π (`∀ x, ¬ (⊤ ∧ ¬ (p x = q x)))
  → π ((¬ (q E = p E) ⇒ Q) = ⊤) ≔
begin
  assume p q E Q hall;
  refine propExt _ _ _ _
  { assume h0; refine ⊤ᵢ }
  { assume h0; refine EAXM92 E hall }
end;

// OPR1_1: (x = E ⇒ P x) = (x = E ⇒ P E), then chain to S.
opaque symbol OPR1_1 [E x : τ ι] (P : τ ι → Prop) [S : Prop]
  : π (((x = E) ⇒ P E) = S)
  → π (((x = E) ⇒ P x) = S) ≔
begin
  assume E x P S h;
  have eq : π (((x = E) ⇒ P x) = ((x = E) ⇒ P E))
  { refine propExt _ _ _ _
    { assume h1 heq; rewrite left heq; refine h1 heq }
    { assume h1 heq; rewrite heq; refine h1 heq } };
  rewrite eq; refine h
end;

// OPR2_1: (E = x ⇒ P x) = (E = x ⇒ P E), then chain to S.
opaque symbol OPR2_1 [E x : τ ι] (P : τ ι → Prop) [S : Prop]
  : π (((E = x) ⇒ P E) = S)
  → π (((E = x) ⇒ P x) = S) ≔
begin
  assume E x P S h;
  have eq : π (((E = x) ⇒ P x) = ((E = x) ⇒ P E))
  { refine propExt _ _ _ _
    { assume h1 heq;
      have heqs : π (x = E) { symmetry; refine heq };
      rewrite left heqs; refine h1 heq }
    { assume h1 heq;
      have heqs : π (x = E) { symmetry; refine heq };
      rewrite heqs; refine h1 heq } };
  rewrite eq; refine h
end;

// EQC1_1: pass-through. ¬((a↦b)=(c↦d))⇒P = (¬(a=c)∨¬(b=d))⇒P.
opaque symbol EQC1_1 [a b c d : τ ι] [P S : Prop]
  : π (((¬ (a = c) ∨ ¬ (b = d)) ⇒ P) = S)
  → π ((¬ ((a ↦ b) = (c ↦ d)) ⇒ P) = S) ≔
begin
  assume a b c d P S h;
  have eq : π ((¬ ((a ↦ b) = (c ↦ d)) ⇒ P) = ((¬ (a = c) ∨ ¬ (b = d)) ⇒ P))
    { refine propExt _ _ _ _
      { assume h1 h2;
        refine h1 _;
        refine ∨ₑ h2 _ _
        { assume hnac h3;
          refine hnac (∧ₑ₁ (pair_inj a b c d h3)) }
        { assume hnbd h3;
          refine hnbd (∧ₑ₂ (pair_inj a b c d h3)) } }
      { assume h1 h2;
        refine h1 _;
        refine ∨ₑ (em (a = c)) _ _
        { assume hac; refine ∨ₑ (em (b = d)) _ _
          { assume hbd;
            refine ⊥ₑ (h2 (pair_cong a b c d hac hbd)) }
          { assume hnbd; refine ∨ᵢ₂ hnbd } }
        { assume hnac; refine ∨ᵢ₁ hnac } } };
  rewrite eq; refine h
end;

// EQC2_1: pass-through. ((a↦b)=(c↦d))⇒P = (a=c)∧(b=d)⇒P.
opaque symbol EQC2_1 [a b c d : τ ι] [P S : Prop]
  : π (((a = c) ∧ (b = d) ⇒ P) = S)
  → π ((((a ↦ b) = (c ↦ d)) ⇒ P) = S) ≔
begin
  assume a b c d P S h;
  have eq : π ((((a ↦ b) = (c ↦ d)) ⇒ P) = ((a = c) ∧ (b = d) ⇒ P))
    { refine propExt _ _ _ _
      { assume h1 h2; refine h1 (pair_cong a b c d (∧ₑ₁ h2) (∧ₑ₂ h2)) }
      { assume h1 h2; refine h1 (pair_inj a b c d h2) } };
  rewrite eq; refine h
end;

// EQS1_1: pass-through.
opaque symbol EQS1_1 [E F : τ ι] [R S : Prop]
  : π (((E = F) ⇒ R) = S)
  → π (((`∀ x : τ ι, (x ϵ E) ⇔ (x ϵ F)) ⇒ R) = S) ≔
begin
  assume E F R S h;
  have eq : π (((`∀ x : τ ι, (x ϵ E) ⇔ (x ϵ F)) ⇒ R) = ((E = F) ⇒ R))
    { refine propExt _ _ _ _
      { assume h1 h2; refine h1 (∧ₑ₁ (set_ext E F) h2) }
      { assume h1 h2; refine h1 (∧ₑ₂ (set_ext E F) h2) } };
  rewrite eq; refine h
end;

// EQS2_1: structural variant of EQS2.
// Mirrors EQS2: ¬(E=F)⇒R ↔ ¬(eql_set E F)⇒R via set_ext.
opaque symbol EQS2_1 [E F : τ ι] [R S : Prop]
  : π ((¬ (E = F) ⇒ R) = S)
  → π ((¬ (`∀ x : τ ι, (x ϵ E) ⇔ (x ϵ F)) ⇒ R) = S) ≔
begin
  assume E F R S h;
  have eq : π ((¬ (`∀ x : τ ι, (x ϵ E) ⇔ (x ϵ F)) ⇒ R) = (¬ (E = F) ⇒ R))
    { refine propExt _ _ _ _
      { assume h1 h2; refine h1 (λ heqs, ⊥ₑ (h2 (∧ₑ₂ (set_ext E F) heqs))) }
      { assume h1 h2; refine h1 (λ heq, ⊥ₑ (h2 (∧ₑ₁ (set_ext E F) heq))) } };
  rewrite eq; refine h
end;

// ECTR1_1–ECTR6_1: all leaf (schema 0).
opaque symbol ECTR1_1 [E F : τ ι] (Q : τ ι → Prop) [P]
  : π (¬ (Q E))
  → π (Q F)
  → π (((E = F) ⇒ P) = ⊤) ≔
begin
  assume E F Q P hnq hr;
  refine propExt _ _ _ _
  { assume h0; refine ⊤ᵢ }
  { assume h0 heq;
    have hqe : π (Q E) { rewrite heq; refine hr };
    refine ⊥ₑ (hnq hqe) }
end;

opaque symbol ECTR2_1 [E F : τ ι] (Q : τ ι → Prop) [P]
  : π (¬ (Q E))
  → π (Q F)
  → π (((F = E) ⇒ P) = ⊤) ≔
begin
  assume E F Q P hnq hr;
  refine propExt _ _ _ _
  { assume h0; refine ⊤ᵢ }
  { assume h0 heq;
    have hqe : π (Q E) { rewrite left heq; refine hr };
    refine ⊥ₑ (hnq hqe) }
end;

opaque symbol ECTR3_1 [E F : τ ι] (P : τ ι → Prop) [Q]
  : π (E = F)
  → π (P F)
  → π ((¬ (P E) ⇒ Q) = ⊤) ≔
begin
  assume E F P Q heq hr;
  refine propExt _ _ _ _
  { assume h0; refine ⊤ᵢ }
  { assume h0 hnp;
    have hpe : π (P E) { rewrite heq; refine hr };
    refine ⊥ₑ (hnp hpe) }
end;

opaque symbol ECTR4_1 [E F : τ ι] (P : τ ι → Prop) [Q]
  : π (F = E)
  → π (P F)
  → π ((¬ (P E) ⇒ Q) = ⊤) ≔
begin
  assume E F P Q heq hr;
  refine propExt _ _ _ _
  { assume h0; refine ⊤ᵢ }
  { assume h0 hnp;
    have hpe : π (P E) { rewrite left heq; refine hr };
    refine ⊥ₑ (hnp hpe) }
end;

opaque symbol ECTR5_1 [E F : τ ι] (P : τ ι → Prop) [Q]
  : π (E = F)
  → π (¬ (P F))
  → π (((P E) ⇒ Q) = ⊤) ≔
begin
  assume E F P Q heq hnr;
  refine propExt _ _ _ _
  { assume h0; refine ⊤ᵢ }
  { assume h0 hp;
    have hpf : π (P F) { rewrite (eq_sym heq); refine hp };
    refine ⊥ₑ (hnr hpf) }
end;

opaque symbol ECTR6_1 [E F : τ ι] (P : τ ι → Prop) [Q]
  : π (F = E)
  → π (¬ (P F))
  → π (((P E) ⇒ Q) = ⊤) ≔
begin
  assume E F P Q heq hnr;
  refine propExt _ _ _ _
  { assume h0; refine ⊤ᵢ }
  { assume h0 hp;
    have hpf : π (P F) { rewrite heq; refine hp };
    refine ⊥ₑ (hnr hpf) }
end;
