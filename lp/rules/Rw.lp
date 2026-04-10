// Rewrite lemmas for normalisation chains.
// These replace the primed (_1) rule mechanism: instead of equality-chaining
// symbols, the emitter uses `rewrite lemma; ...` sequences.
require open pp2lp.B;

// ---- Structural connectors ----

// Schema 2: lift independent equalities into a conjunction equality.
opaque symbol conj_eq [A B S1 S2 : Prop]
  : π (A = S1) → π (B = S2) → π ((A ∧ B) = (S1 ∧ S2)) ≔
begin
  assume A B S1 S2 h1 h2;
  rewrite h1; rewrite h2; reflexivity
end;

// IMP4'/ALL9': lift equality under implication (conditional on hypothesis).
opaque symbol imp_cong [P Q R : Prop]
  : (π P → π (Q = R)) → π ((P ⇒ Q) = (P ⇒ R)) ≔
begin
  assume P Q R h;
  refine propExt _ _ _ _
    { assume h1 hp; refine =⇒ (h hp) (h1 hp) }
    { assume h1 hp; refine =⇒ (eq_sym (h hp)) (h1 hp) }
end;

// ALL8': lift equality under ∀.
opaque symbol forall_cong [P R : τ ι → Prop]
  : (Π x : τ ι, π (P x = R x)) → π ((`∀ x : τ ι, P x) = (`∀ x : τ ι, R x)) ≔
begin
  assume P R h;
  refine propExt _ _ _ _
    { assume h1 x; refine =⇒ (h x) (h1 x) }
    { assume h1 x; refine =⇒ (eq_sym (h x)) (h1 x) }
end;

// AND5': lift antecedent equivalence into implication equality.
opaque symbol ante_cong [C C' R : Prop]
  : (π C → π C') → (π C' → π C) → π ((C ⇒ R) = (C' ⇒ R)) ≔
begin
  assume C C' R fwd bwd;
  refine propExt _ _ _ _
    { assume h hc'; refine h (bwd hc') }
    { assume h hc; refine h (fwd hc) }
end;

// ---- Conjunction (§A.1) ----

// AND1: ¬(P∧Q)⇒R = (¬Q⇒R) ∧ (¬P⇒R)
opaque symbol and1_eq [P Q R : Prop]
  : π ((¬ (P ∧ Q) ⇒ R) = ((¬ Q ⇒ R) ∧ (¬ P ⇒ R))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h; refine ∧ᵢ
      (λ hnq, h (λ hpq, hnq (∧ₑ₂ hpq)))
      (λ hnp, h (λ hpq, hnp (∧ₑ₁ hpq))) }
    { assume h hnpq;
      have hnpnq : π (¬ P ∨ ¬ Q) { refine =⇒ (deMorgan_∧ P Q) hnpq };
      refine ∨ₑ hnpnq _ _
      { assume hnp; refine ∧ₑ₂ h hnp }
      { assume hnq; refine ∧ₑ₁ h hnq } }
end;

// AND2: ¬(P∧Q) = (P⇒¬Q)
opaque symbol and2_eq [P Q : Prop]
  : π (¬ (P ∧ Q) = (P ⇒ ¬ Q)) ≔
begin
  assume P Q;
  refine propExt _ _ _ _
    { assume h1 hp hq; refine h1 (∧ᵢ hp hq) }
    { assume h1 h2; refine h1 (∧ₑ₁ h2) (∧ₑ₂ h2) }
end;

// AND3: (P∧Q)⇒R = (P⇒Q⇒R)
opaque symbol and3_eq [P Q R : Prop]
  : π (((P ∧ Q) ⇒ R) = (P ⇒ Q ⇒ R)) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h1 hp hq; refine h1 (∧ᵢ hp hq) }
    { assume h1 h2; refine h1 (∧ₑ₁ h2) (∧ₑ₂ h2) }
end;

// ---- Disjunction (§A.2) ----

// OR1: ¬(P∨Q)⇒R = (¬P⇒¬Q⇒R)
opaque symbol or1_eq [P Q R : Prop]
  : π ((¬ (P ∨ Q) ⇒ R) = (¬ P ⇒ (¬ Q ⇒ R))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h1 hnp hnq;
      have hnpq : π (¬ (P ∨ Q))
        { assume hpq; refine ∨ₑ hpq _ _
          { assume hp; refine hnp hp }
          { assume hq; refine hnq hq } };
      refine h1 hnpq }
    { assume h1 hnpq;
      have hnpnq : π (¬ P ∧ ¬ Q) { refine =⇒ (deMorgan_∨ P Q) hnpq };
      refine h1 (∧ₑ₁ hnpnq) (∧ₑ₂ hnpnq) }
end;

// OR2: ¬(P∨Q) = (¬Q ∧ ¬P)
opaque symbol or2_eq [P Q : Prop]
  : π (¬ (P ∨ Q) = (¬ Q ∧ ¬ P)) ≔
begin
  assume P Q;
  rewrite deMorgan_∨;
  rewrite ∧_com;
  reflexivity
end;

// OR3: (P∨Q)⇒R = (Q⇒R) ∧ (P⇒R)
opaque symbol or3_eq [P Q R : Prop]
  : π (((P ∨ Q) ⇒ R) = ((Q ⇒ R) ∧ (P ⇒ R))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h; refine ∧ᵢ (λ hq, h (∨ᵢ₂ hq)) (λ hp, h (∨ᵢ₁ hp)) }
    { assume h hpq; refine ∨ₑ hpq _ _
      { assume hp; refine ∧ₑ₂ h hp }
      { assume hq; refine ∧ₑ₁ h hq } }
end;

// OR4: P∨Q = (¬P⇒Q). P and Q explicit to avoid HO unification issues.
opaque symbol or4_eq (P Q : Prop)
  : π ((P ∨ Q) = (¬ P ⇒ Q)) ≔
begin
  assume P Q;
  refine propExt _ _ _ _
    { assume hpq hnp; refine ∨ₑ hpq _ _
      { assume hp; refine ⊥ₑ (hnp hp) }
      { assume hq; refine hq } }
    { assume h1; refine ∨ₑ (em P) _ _
      { assume hp; refine ∨ᵢ₁ hp }
      { assume hnp; refine ∨ᵢ₂ (h1 hnp) } }
end;

// AND4: (P ∧ Q) = (Q ∧ P) (commutativity — no connective transformation)
// No dedicated lemma needed: emit `rewrite ∧_com; refine conj_eq ...`

// IMP2: ¬(P⇒Q) = (¬Q ∧ P)
opaque symbol imp2_eq [P Q : Prop]
  : π (¬ (P ⇒ Q) = (¬ Q ∧ P)) ≔
begin
  assume P Q;
  rewrite ¬⇒=∧¬;
  rewrite ∧_com;
  reflexivity
end;

// ---- Implication (§A.3) ----

// IMP1: ¬(P⇒Q)⇒R = (P⇒¬Q⇒R)
opaque symbol imp1_eq [P Q R : Prop]
  : π ((¬ (P ⇒ Q) ⇒ R) = (P ⇒ (¬ Q ⇒ R))) ≔
begin
  assume P Q R;
  rewrite ¬⇒=∧¬;
  refine propExt _ _ _ _
    { assume h1 hp hnq; refine h1 (∧ᵢ hp hnq) }
    { assume h1 h2; refine h1 (∧ₑ₁ h2) (∧ₑ₂ h2) }
end;

// IMP3: (P⇒Q)⇒R = (Q⇒R) ∧ (¬P⇒R)
opaque symbol imp3_eq [P Q R : Prop]
  : π (((P ⇒ Q) ⇒ R) = ((Q ⇒ R) ∧ (¬ P ⇒ R))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h; refine ∧ᵢ
      (λ hq, h (λ h0, hq))
      (λ hnp, h (λ hp, ⊥ₑ (hnp hp))) }
    { assume h hpq; refine ∨ₑ (em P) _ _
      { assume hp; refine ∧ₑ₁ h (hpq hp) }
      { assume hnp; refine ∧ₑ₂ h hnp } }
end;

// ---- Equivalence (§A.4) ----

// EQV1: ¬(P⇔Q)⇒R = (P⇒¬Q⇒R) ∧ (¬P⇒Q⇒R)
opaque symbol eqv1_eq [P Q R : Prop]
  : π ((¬ (P ⇔ Q) ⇒ R) = ((P ⇒ (¬ Q ⇒ R)) ∧ (¬ P ⇒ (Q ⇒ R)))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h; refine ∧ᵢ
      (λ hp hnq, h (λ heqv, hnq (∧ₑ₁ heqv hp)))
      (λ hnp hq, h (λ heqv, hnp (∧ₑ₂ heqv hq))) }
    { assume h hneqv;
      refine ∨ₑ (em P) _ _
      { assume hp; refine ∨ₑ (em Q) _ _
        { assume hq;
          have heqv : π (P ⇔ Q) { refine ∧ᵢ (λ h0, hq) (λ h0, hp) };
          refine ⊥ₑ (hneqv heqv) }
        { assume hnq; refine ∧ₑ₁ h hp hnq } }
      { assume hnp; refine ∨ₑ (em Q) _ _
        { assume hq; refine ∧ₑ₂ h hnp hq }
        { assume hnq;
          have heqv : π (P ⇔ Q)
            { refine ∧ᵢ (λ hp, ⊥ₑ (hnp hp)) (λ hq, ⊥ₑ (hnq hq)) };
          refine ⊥ₑ (hneqv heqv) } } }
end;

// EQV2: ¬(P⇔Q) = (P⇒¬Q) ∧ (¬Q⇒P)
opaque symbol eqv2_eq [P Q : Prop]
  : π (¬ (P ⇔ Q) = ((P ⇒ ¬ Q) ∧ (¬ Q ⇒ P))) ≔
begin
  assume P Q;
  refine propExt _ _ _ _
    { assume hneqv; refine ∧ᵢ
      (λ hp hq, hneqv (∧ᵢ (λ h0, hq) (λ h0, hp)))
      (λ hnq, ¬¬ₑ P (λ hnp, hneqv (∧ᵢ
        (λ hp, ⊥ₑ (hnp hp))
        (λ hq, ⊥ₑ (hnq hq))))) }
    { assume h heqv;
      have hpnq : π (P ⇒ ¬ Q) { refine ∧ₑ₁ h };
      have hnqp : π (¬ Q ⇒ P) { refine ∧ₑ₂ h };
      refine ∨ₑ (em Q) _ _
      { assume hq;
        have hp : π P { refine ∧ₑ₂ heqv hq };
        refine hpnq hp hq }
      { assume hnq;
        have hp : π P { refine hnqp hnq };
        have hq : π Q { refine ∧ₑ₁ heqv hp };
        refine hnq hq } }
end;

// EQV3: (P⇔Q)⇒R = (P⇒Q⇒R) ∧ (¬P⇒¬Q⇒R)
opaque symbol eqv3_eq [P Q R : Prop]
  : π (((P ⇔ Q) ⇒ R) = ((P ⇒ (Q ⇒ R)) ∧ (¬ P ⇒ (¬ Q ⇒ R)))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h; refine ∧ᵢ
      (λ hp hq, h (∧ᵢ (λ h0, hq) (λ h0, hp)))
      (λ hnp hnq, h (∧ᵢ
        (λ hp, ⊥ₑ (hnp hp))
        (λ hq, ⊥ₑ (hnq hq)))) }
    { assume h heqv;
      refine ∨ₑ (em P) _ _
      { assume hp;
        have hq : π Q { refine ∧ₑ₁ heqv hp };
        refine ∧ₑ₁ h hp hq }
      { assume hnp;
        refine ∨ₑ (em Q) _ _
        { assume hq;
          have hp : π P { refine ∧ₑ₂ heqv hq };
          refine ⊥ₑ (hnp hp) }
        { assume hnq; refine ∧ₑ₂ h hnp hnq } } }
end;

// EQV4: (P⇔Q) = (P⇒Q) ∧ (Q⇒P)
opaque symbol eqv4_eq [P Q : Prop]
  : π ((P ⇔ Q) = ((P ⇒ Q) ∧ (Q ⇒ P))) ≔
begin
  assume P Q;
  refine propExt _ _ _ _
    { assume h; refine h }
    { assume h; refine h }
end;

// ---- Negation (§A.5) ----

// NOT1: ¬¬P⇒R = (P⇒R)
opaque symbol not1_eq [P R : Prop]
  : π ((¬ ¬ P ⇒ R) = (P ⇒ R)) ≔
begin
  assume P R;
  refine propExt _ _ _ _
    { assume h1 hp; refine h1 (λ hnp, hnp hp) }
    { assume h1 hnnp; refine h1 (¬¬ₑ P hnnp) }
end;

// ---- Equality (§A.13) ----

// EVR3: (E=E)⇒P = P
opaque symbol evr3_eq [E : τ ι] [P : Prop]
  : π (((E = E) ⇒ P) = P) ≔
begin
  assume E P;
  refine propExt _ _ _ _
    { assume h1; refine h1 (eq_refl E) }
    { assume h1 h2; refine h1 }
end;

// OPR1: (x=E)⇒P(x) = (x=E)⇒P(E)
opaque symbol opr1_eq [E x : τ ι] [P : τ ι → Prop]
  : π (((x = E) ⇒ P x) = ((x = E) ⇒ P E)) ≔
begin
  assume E x P;
  refine propExt _ _ _ _
    { assume h1 heq; rewrite left heq; refine h1 heq }
    { assume h1 heq; rewrite heq; refine h1 heq }
end;

// OPR2: (E=x)⇒P(x) = (E=x)⇒P(E)
opaque symbol opr2_eq [E x : τ ι] [P : τ ι → Prop]
  : π (((E = x) ⇒ P x) = ((E = x) ⇒ P E)) ≔
begin
  assume E x P;
  refine propExt _ _ _ _
    { assume h1 heq;
      have heqs : π (x = E) { symmetry; refine heq };
      rewrite left heqs; refine h1 heq }
    { assume h1 heq;
      have heqs : π (x = E) { symmetry; refine heq };
      rewrite heqs; refine h1 heq }
end;

// EQC1: ¬(a↦b = c↦d)⇒P = (¬(a=c) ∨ ¬(b=d))⇒P
opaque symbol eqc1_eq [a b c d : τ ι] [P : Prop]
  : π ((¬ ((a ↦ b) = (c ↦ d)) ⇒ P) = ((¬ (a = c) ∨ ¬ (b = d)) ⇒ P)) ≔
begin
  assume a b c d P;
  refine propExt _ _ _ _
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
      { assume hnac; refine ∨ᵢ₁ hnac } }
end;

// EQC2: (a↦b = c↦d)⇒P = (a=c ∧ b=d)⇒P
opaque symbol eqc2_eq [a b c d : τ ι] [P : Prop]
  : π ((((a ↦ b) = (c ↦ d)) ⇒ P) = (((a = c) ∧ (b = d)) ⇒ P)) ≔
begin
  assume a b c d P;
  refine propExt _ _ _ _
    { assume h1 h2; refine h1 (pair_cong a b c d (∧ₑ₁ h2) (∧ₑ₂ h2)) }
    { assume h1 h2; refine h1 (pair_inj a b c d h2) }
end;

// EQS1: (∀x. x∈E ⇔ x∈F)⇒R = (E=F)⇒R
opaque symbol eqs1_eq [E F : τ ι] [R : Prop]
  : π (((`∀ x : τ ι, (x ϵ E) ⇔ (x ϵ F)) ⇒ R) = ((E = F) ⇒ R)) ≔
begin
  assume E F R;
  refine propExt _ _ _ _
    { assume h1 h2; refine h1 (∧ₑ₁ (set_ext E F) h2) }
    { assume h1 h2; refine h1 (∧ₑ₂ (set_ext E F) h2) }
end;

// EQS2: ¬(∀x. x∈E ⇔ x∈F)⇒R = ¬(E=F)⇒R
opaque symbol eqs2_eq [E F : τ ι] [R : Prop]
  : π ((¬ (`∀ x : τ ι, (x ϵ E) ⇔ (x ϵ F)) ⇒ R) = (¬ (E = F) ⇒ R)) ≔
begin
  assume E F R;
  refine propExt _ _ _ _
    { assume h1 h2; refine h1 (λ heqs, ⊥ₑ (h2 (∧ₑ₂ (set_ext E F) heqs))) }
    { assume h1 h2; refine h1 (λ heq, ⊥ₑ (h2 (∧ₑ₁ (set_ext E F) heq))) }
end;

// EIMP51: ¬(E=F)⇒P = P (when ¬(F=E) is known)
opaque symbol eimp51_eq [E F : τ ι] [P : Prop]
  : π (¬ (F = E)) → π ((¬ (E = F) ⇒ P) = P) ≔
begin
  assume E F P hneq;
  refine propExt _ _ _ _
    { assume h1; refine h1 (λ h2, hneq (eq_sym h2)) }
    { assume h1 h2; refine h1 }
end;

// EIMP52: (E=F)⇒P = P (when F=E is known)
opaque symbol eimp52_eq [E F : τ ι] [P : Prop]
  : π (F = E) → π (((E = F) ⇒ P) = P) ≔
begin
  assume E F P heq;
  refine propExt _ _ _ _
    { assume h1; refine h1 (eq_sym heq) }
    { assume h1 h2; refine h1 }
end;

// AR9: (E ≤ 0) ⇒ R = (F ≤ 0) ⇒ R (from E = F)
opaque symbol ar9_eq [E : τ ι] (F : τ ι) [R : Prop]
  : π (E = F)
  → π (((E ≤ 𝟎) ⇒ R) = ((F ≤ 𝟎) ⇒ R)) ≔
begin
  assume E F R heq;
  rewrite heq; reflexivity
end;

// ---- Existential (§A.8) ----

// XST7: (∃x.P x)⇒R = ∀x.(P x⇒R)
opaque symbol xst7_eq [P : τ ι → Prop] [R : Prop]
  : π (((`∃ x, P x) ⇒ R) = (`∀ x, P x ⇒ R)) ≔
begin
  assume P R;
  refine propExt _ _ _ _
    { assume h1 x hpx; refine h1 (∃ᵢ x hpx) }
    { assume h1 hex; refine ∃ₑ hex h1 }
end;

// ---- _1 equality combinators ----
// Each _1 rule takes child equalities and produces the parent equality.
// These compose as terms: AND3_1 (IMP4_1 (STOP_1)) : π (P = R).

// Transitivity (needed for passthrough _1 rules)
opaque symbol eq_trans [P Q R : Prop]
  : π (P = Q) → π (Q = R) → π (P = R) ≔
begin assume P Q R h1 h2; rewrite h1; refine h2 end;

// STOP_1: leaf — identity
opaque symbol STOP_1 [P : Prop] : π (P = P) ≔
begin assume P; reflexivity end;

// ---- Structural _1 rules ----

// IMP4_1: congruence of ⇒ on the right (unconditional)
opaque symbol IMP4_1 [P Q R : Prop]
  : π (Q = R) → π ((P ⇒ Q) = (P ⇒ R)) ≔
begin assume P Q R h; rewrite h; reflexivity end;

// IMP5_1: strip known antecedent (needs proof of P)
opaque symbol IMP5_1 [P Q S : Prop]
  : π P → π (Q = S) → π ((P ⇒ Q) = S) ≔
begin
  assume P Q S hp hqs;
  refine propExt _ _ _ _
  { assume hpq; refine =⇒ hqs (hpq hp) }
  { assume hs hp2; refine =⇒ (eq_sym hqs) hs }
end;

// ALL8_1: congruence under ∀
opaque symbol ALL8_1 [P R : τ ι → Prop]
  : (Π x : τ ι, π (P x = R x))
  → π ((`∀ x, P x) = (`∀ x, R x)) ≔
begin
  assume P R h;
  refine propExt _ _ _ _
  { assume h1 x; refine =⇒ (h x) (h1 x) }
  { assume h1 x; refine =⇒ (eq_sym (h x)) (h1 x) }
end;

// NRM1_1: strip constant ♢ under equality.
// (♢ _, P) ⇒ Q = S  →  P ⇒ Q = S  (when P doesn't depend on bound var)
opaque symbol NRM1_1 [P Q S : Prop]
  : π ((P ⇒ Q) = S)
  → π (((`♢ _ : τ ι, P) ⇒ Q) = S) ≔
begin
  assume P Q S h;
  have h1 : π ((`♢ _ : τ ι, P) = P)
    { refine ∀_const ι P };
  have h2 : π (((`♢ _ : τ ι, P) ⇒ Q) = (P ⇒ Q))
    { rewrite h1; reflexivity };
  refine eq_trans h2 h
end;

// ALL7_1: equality for branching quantifier in _1 chain.
// Composes inner per-element equality with continuation equality.
opaque symbol ALL7_1 [P : τ ι → Prop] [Q S : Prop]
  :  π (((`♢ x, P x) ⇒ Q) = S)
  → π (((`∀ x, P x) ⇒ Q) = S) ≔
begin
admit
end;

// XST8_1: equality for existential ¬¬-elimination in _1 chain.
// ∃x.P(x) = ((∀x, ¬P(x)) ⇒ ⊥ = S) → (∃x.P(x) = S)
opaque symbol XST8_1 [P : τ ι → Prop] [S : Prop]
  : π (((`∀ x, ¬ (P x)) ⇒ ⊥) = S)
  → π ((`∃ x, P x) = S) ≔
begin
  assume P S h;
  have h1 : π ((`∃ x, P x) = ((`∀ x, ¬ (P x)) ⇒ ⊥))
    { refine propExt _ _ _ _
      { assume hex hall; refine ∃ₑ hex (λ x hpx, hall x hpx) }
      { assume hc; refine ¬¬ₑ _ (λ hne, hc (λ x hpx, hne (∃ᵢ x hpx))) } };
  refine eq_trans h1 h
end;

// ALL9_1: congruence under hypothesis implication (same as IMP4_1)
opaque symbol ALL9_1 [H Q R : Prop]
  : π (Q = R) → π ((H ⇒ Q) = (H ⇒ R)) ≔
begin assume H Q R h; rewrite h; reflexivity end;

// ---- Passthrough _1 rules (eq_trans local_eq child_eq) ----

opaque symbol AND2_1 [P Q S : Prop]
  : π ((P ⇒ ¬ Q) = S) → π (¬ (P ∧ Q) = S) ≔
begin assume P Q S h; refine eq_trans (and2_eq) h end;

opaque symbol AND3_1 [P Q R S : Prop]
  : π ((P ⇒ Q ⇒ R) = S) → π (((P ∧ Q) ⇒ R) = S) ≔
begin assume P Q R S h; refine eq_trans and3_eq h end;

opaque symbol OR1_1 [P Q R S : Prop]
  : π ((¬ P ⇒ ¬ Q ⇒ R) = S) → π ((¬ (P ∨ Q) ⇒ R) = S) ≔
begin assume P Q R S h; refine eq_trans or1_eq h end;

opaque symbol OR4_1 [P Q S : Prop]
  : π ((¬ P ⇒ Q) = S) → π ((P ∨ Q) = S) ≔
begin assume P Q S h; refine eq_trans (or4_eq P Q) h end;

opaque symbol NOT1_1 [P R S : Prop]
  : π ((P ⇒ R) = S) → π ((¬ ¬ P ⇒ R) = S) ≔
begin assume P R S h; refine eq_trans not1_eq h end;

opaque symbol NOT2_1 [P S : Prop]
  : π (P = S) → π (¬ ¬ P = S) ≔
begin assume P S h; refine eq_trans (¬¬ₑ_eq P) h end;

opaque symbol IMP1_1 [P Q R S : Prop]
  : π ((P ⇒ ¬ Q ⇒ R) = S) → π ((¬ (P ⇒ Q) ⇒ R) = S) ≔
begin assume P Q R S h; refine eq_trans imp1_eq h end;

opaque symbol VR3_1 [P S : Prop]
  : π (P = S) → π ((⊤ ⇒ P) = S) ≔
begin assume P S h; refine eq_trans (⊤⇒ P) h end;

opaque symbol EVR2_1 [E : τ ι] [S : Prop]
  : π (⊥ = S) → π (¬ (E = E) = S) ≔
begin assume E S h; refine eq_trans (¬=_idem ι E) h end;

opaque symbol EVR3_1 [E : τ ι] [P S : Prop]
  : π (P = S) → π (((E = E) ⇒ P) = S) ≔
begin
  assume E P S h;
  have h1 : π ((E = E) = ⊤) { refine =_idem ι E };
  have h2 : π (((E = E) ⇒ P) = (⊤ ⇒ P))
    { rewrite h1; reflexivity };
  refine eq_trans h2 (eq_trans (⊤⇒ P) h)
end;

// ---- Branching _1 rules (eq_trans local_eq (conj_eq child1 child2)) ----

opaque symbol AND1_1 [P Q R S1 S2 : Prop]
  : π ((¬ Q ⇒ R) = S1) → π ((¬ P ⇒ R) = S2)
  → π ((¬ (P ∧ Q) ⇒ R) = (S1 ∧ S2)) ≔
begin assume P Q R S1 S2 h1 h2; refine eq_trans and1_eq (conj_eq h1 h2) end;

opaque symbol AND4_1 [P Q S1 S2 : Prop]
  : π (Q = S1) → π (P = S2) → π ((P ∧ Q) = (S1 ∧ S2)) ≔
begin
  assume P Q S1 S2 h1 h2;
  refine eq_trans (∧_com P Q) (conj_eq h1 h2)
end;

opaque symbol OR2_1 [P Q S1 S2 : Prop]
  : π ((¬ Q) = S1) → π ((¬ P) = S2)
  → π (¬ (P ∨ Q) = (S1 ∧ S2)) ≔
begin assume P Q S1 S2 h1 h2; refine eq_trans or2_eq (conj_eq h1 h2) end;

opaque symbol OR3_1 [P Q R S1 S2 : Prop]
  : π ((Q ⇒ R) = S1) → π ((P ⇒ R) = S2)
  → π (((P ∨ Q) ⇒ R) = (S1 ∧ S2)) ≔
begin assume P Q R S1 S2 h1 h2; refine eq_trans or3_eq (conj_eq h1 h2) end;

opaque symbol IMP3_1 [P Q R S1 S2 : Prop]
  : π ((Q ⇒ R) = S1) → π ((¬ P ⇒ R) = S2)
  → π (((P ⇒ Q) ⇒ R) = (S1 ∧ S2)) ≔
begin assume P Q R S1 S2 h1 h2; refine eq_trans imp3_eq (conj_eq h1 h2) end;

opaque symbol IMP2_1 [P Q S1 S2 : Prop]
  : π ((¬ Q) = S1) → π (P = S2)
  → π (¬ (P ⇒ Q) = (S1 ∧ S2)) ≔
begin assume P Q S1 S2 h1 h2; refine eq_trans imp2_eq (conj_eq h1 h2) end;

opaque symbol EQV1_1 [P Q R S1 S2 : Prop]
  : π ((P ⇒ ¬ Q ⇒ R) = S1) → π ((¬ P ⇒ Q ⇒ R) = S2)
  → π ((¬ (P ⇔ Q) ⇒ R) = (S1 ∧ S2)) ≔
begin assume P Q R S1 S2 h1 h2; refine eq_trans eqv1_eq (conj_eq h1 h2) end;

opaque symbol EQV3_1 [P Q R S1 S2 : Prop]
  : π ((P ⇒ Q ⇒ R) = S1) → π ((¬ P ⇒ ¬ Q ⇒ R) = S2)
  → π (((P ⇔ Q) ⇒ R) = (S1 ∧ S2)) ≔
begin assume P Q R S1 S2 h1 h2; refine eq_trans eqv3_eq (conj_eq h1 h2) end;
