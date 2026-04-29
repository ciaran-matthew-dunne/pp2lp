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

// Conjunction associativity (right → left).
// Applied via `rewrite ∧_assoc` inside ALL7_2/XST8_2 continuations to
// reshape the right-associated R (as produced by the _1 chain) into the
// left-associated form that the PP-recorded tactics expect.
opaque symbol ∧_assoc [A B C : Prop]
  : π ((A ∧ (B ∧ C)) = ((A ∧ B) ∧ C)) ≔
begin
  assume A B C;
  refine propExt _ _ _ _
  { assume h; refine ∧ᵢ (∧ᵢ (∧ₑ₁ h) (∧ₑ₁ (∧ₑ₂ h))) (∧ₑ₂ (∧ₑ₂ h)) }
  { assume h; refine ∧ᵢ (∧ₑ₁ (∧ₑ₁ h)) (∧ᵢ (∧ₑ₂ (∧ₑ₁ h)) (∧ₑ₂ h)) }
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
// R is the per-element result; inner chain proves P x = R x for each x.
opaque symbol ALL7_1 [P : τ ι → Prop] (R : τ ι → Prop) [Q S : Prop]
  : (Π x : τ ι, π (P x = R x))
  → π (((`♢ x, R x) ⇒ Q) = S)
  → π (((`∀ x, P x) ⇒ Q) = S) ≔
begin
  assume P R Q S h1 h2;
  have h3 : π ((`∀ x, P x) = (`∀ x, R x))
    { refine ALL8_1 h1 };
  have h4 : π (((`∀ x, P x) ⇒ Q) = ((`∀ x, R x) ⇒ Q))
    { rewrite h3; reflexivity };
  refine eq_trans h4 h2
end;

// ALL7_1_2: Two-variable version.
opaque symbol ALL7_1_2 [P : τ ι → τ ι → Prop] (R : τ ι → τ ι → Prop) [Q S : Prop]
  : (Π x : τ ι, Π y : τ ι, π (P x y = R x y))
  → π (((`♢ x, `♢ y, R x y) ⇒ Q) = S)
  → π (((`∀ x, `∀ y, P x y) ⇒ Q) = S) ≔
begin
  assume P R Q S h1 h2;
  have h3 : π ((`∀ x, `∀ y, P x y) = (`∀ x, `∀ y, R x y))
    { refine ALL8_1 (λ x, ALL8_1 (h1 x)) };
  have h4 : π (((`∀ x, `∀ y, P x y) ⇒ Q) = ((`∀ x, `∀ y, R x y) ⇒ Q))
    { rewrite h3; reflexivity };
  refine eq_trans h4 h2
end;

// ALL7_1_3: Three-variable version.
opaque symbol ALL7_1_3 [P : τ ι → τ ι → τ ι → Prop] (R : τ ι → τ ι → τ ι → Prop) [Q S : Prop]
  : (Π x : τ ι, Π y : τ ι, Π z : τ ι, π (P x y z = R x y z))
  → π (((`♢ x, `♢ y, `♢ z, R x y z) ⇒ Q) = S)
  → π (((`∀ x, `∀ y, `∀ z, P x y z) ⇒ Q) = S) ≔
begin
  assume P R Q S h1 h2;
  have h3 : π ((`∀ x, `∀ y, `∀ z, P x y z) = (`∀ x, `∀ y, `∀ z, R x y z))
    { refine ALL8_1 (λ x, ALL8_1 (λ y, ALL8_1 (h1 x y))) };
  have h4 : π (((`∀ x, `∀ y, `∀ z, P x y z) ⇒ Q) = ((`∀ x, `∀ y, `∀ z, R x y z) ⇒ Q))
    { rewrite h3; reflexivity };
  refine eq_trans h4 h2
end;

// XST7_1: equality for (∃x.P x ⇒ R) normalising to (∀x. P x ⇒ R).
opaque symbol XST7_1 [P : τ ι → Prop] [R S : Prop]
  : π ((`∀ x, P x ⇒ R) = S)
  → π (((`∃ x, P x) ⇒ R) = S) ≔
begin
  assume P R S h;
  have h1 : π (((`∃ x, P x) ⇒ R) = (`∀ x, P x ⇒ R))
    { refine propExt _ _ _ _
      { assume hir x hpx; refine hir (∃ᵢ x hpx) }
      { assume hall hex; refine ∃ₑ hex hall } };
  refine eq_trans h1 h
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

// XST8_1_2: Two-variable version.
opaque symbol XST8_1_2 [P : τ ι → τ ι → Prop] [S : Prop]
  : π (((`∀ x, `∀ y, ¬ (P x y)) ⇒ ⊥) = S)
  → π ((`∃ x, `∃ y, P x y) = S) ≔
begin
  assume P S h;
  have h1 : π ((`∃ x, `∃ y, P x y) = ((`∀ x, `∀ y, ¬ (P x y)) ⇒ ⊥))
    { refine propExt _ _ _ _
      { assume hex hall; refine ∃ₑ hex (λ x hexy, ∃ₑ hexy (λ y hpxy, hall x y hpxy)) }
      { assume hc; refine ¬¬ₑ _ (λ hne, hc (λ x y hpxy, hne (∃ᵢ x (∃ᵢ y hpxy)))) } };
  refine eq_trans h1 h
end;

// XST8_1_3: Three-variable version.
opaque symbol XST8_1_3 [P : τ ι → τ ι → τ ι → Prop] [S : Prop]
  : π (((`∀ x, `∀ y, `∀ z, ¬ (P x y z)) ⇒ ⊥) = S)
  → π ((`∃ x, `∃ y, `∃ z, P x y z) = S) ≔
begin
  assume P S h;
  have h1 : π ((`∃ x, `∃ y, `∃ z, P x y z) = ((`∀ x, `∀ y, `∀ z, ¬ (P x y z)) ⇒ ⊥))
    { refine propExt _ _ _ _
      { assume hex hall;
        refine ∃ₑ hex (λ x hexy, ∃ₑ hexy (λ y hexz, ∃ₑ hexz (λ z hpxyz, hall x y z hpxyz))) }
      { assume hc; refine ¬¬ₑ _ (λ hne, hc (λ x y z hpxyz, hne (∃ᵢ x (∃ᵢ y (∃ᵢ z hpxyz))))) } };
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

// OPR1_1/OPR2_1: PP's primed one-point-rule. Inside a `_1` chain, the
// step rewrites `(x = E ⇒ P x)` to `(x = E ⇒ P E)` (OPR1) or the
// symmetric `(E = x ⇒ P x)` to `(E = x ⇒ P E)` (OPR2). The bridge
// equality `(x = E ⇒ P x) = (x = E ⇒ P E)` holds pointwise: when
// `x = E` is true, both sides reduce to `P E`; when false, both are
// vacuously `⊤`. No surrounding binder is required.
opaque symbol OPR1_1 [E : τ ι] [S : Prop] (P : τ ι → Prop) (x : τ ι)
  : π ((x = E ⇒ P E) = S) → π ((x = E ⇒ P x) = S) ≔
begin
  assume E S P x h;
  have bridge : π ((x = E ⇒ P x) = (x = E ⇒ P E))
    { refine propExt _ _ _ _
        { assume hyp hxe; have px : π (P x) { refine hyp hxe };
          rewrite left hxe; refine px }
        { assume hyp hxe; have pe : π (P E) { refine hyp hxe };
          rewrite hxe; refine pe } };
  refine eq_trans bridge h
end;

opaque symbol OPR2_1 [E : τ ι] [S : Prop] (P : τ ι → Prop) (x : τ ι)
  : π ((E = x ⇒ P E) = S) → π ((E = x ⇒ P x) = S) ≔
begin
  assume E S P x h;
  have bridge : π ((E = x ⇒ P x) = (E = x ⇒ P E))
    { refine propExt _ _ _ _
        { assume hyp hex; have px : π (P x) { refine hyp hex };
          rewrite hex; refine px }
        { assume hyp hex; have pe : π (P E) { refine hyp hex };
          rewrite left hex; refine pe } };
  refine eq_trans bridge h
end;

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
