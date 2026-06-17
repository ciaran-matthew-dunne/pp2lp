// Equality rules (§A.13) — shallow encoding
// Exp ≃ Exp becomes Leibniz equality (polymorphic)
require open pp2lp.B pp2lp.lemmas.Int pp2lp.lemmas.Tuple pp2lp.rules.Res;

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
  : π (⋀ (∎ ∷ (a = c) ∷ (b = d)) ⇒ P)
  → π (((a ↦ b) = (c ↦ d)) ⇒ P) ≔
begin
  assume a b c d P h1 h2;
  refine h1 (⋀₂_intro (∧ₑ₁ (pair_inj a b c d h2)) (∧ₑ₂ (pair_inj a b c d h2)))
end;

// ---- EQS (set equality) ----
// eql_set(E,F) is modeled as ∀x.(x∈E ⇔ x∈F) (set extensionality).

symbol eql_set (X Y : τ ι) ≔
  (`∀ a, (a ϵ X) ⇔ (a ϵ Y));

// eql_set E F = (E = F), as a propositional equality (set extensionality).
opaque symbol eql_set_eq [E F : τ ι] : π (eql_set E F = (E = F)) ≔
begin
  assume E F;
  refine propExt _ _ (λ h, ∧ₑ₂ (set_ext E F) h) (λ h, ∧ₑ₁ (set_ext E F) h)
end;

// EQS1: H ⊢ (E=F) ⇒ R → H ⊢ eql_set(E,F) ⇒ R
// From (E=F)⇒R, derive (∀x.x∈E⇔x∈F)⇒R.
opaque symbol EQS1 [E F : τ ι] [R]
  : π ((E = F) ⇒ R)
  → π (eql_set E F ⇒ R) ≔
begin
  assume E F R h1 h2;
  refine h1 (∧ₑ₂ (set_ext E F) h2)
end;


// EQS2: H ⊢ FAUX ⇒ R → H ⊢ ¬eql_set(E,F) ⇒ R
// The spec (§10.4.3, p.98) really does take FAUX ⇒ R as the premise: PP
// deliberately skips the marker's proof ("ne pas tenir compte de la
// preuve d'un tel prédicat"), sound because the marker — or the equality
// it stands for — is still in PP's hypothesis store.  The emitter
// recovers that store fact and passes it as the explicit first argument.
opaque symbol EQS2 [E F : τ ι] [R]
  : π (eql_set E F)
  → π (⊥ ⇒ R)
  → π (¬ eql_set E F ⇒ R) ≔
begin
  assume E F R hev hbot hneg;
  refine hbot (hneg hev)
end;

// EQS2 store evidence when only the *inclusions* are in scope (the
// equality hyp itself was split into another branch): rebuild
// `eql_set E F` from the two refuted-inclusion universals PP's
// normalisation leaves in H (`forall2(x).not(x:E and not(x:F))`).
opaque symbol eql_set_intro [E F : τ ι]
  (h1 : π (`!! v : Tuple 1, ¬ (⋀ ((∎ ∷ (prj 0 v ϵ E)) ∷ (¬ (prj 0 v ϵ F))))))
  (h2 : π (`!! v : Tuple 1, ¬ (⋀ ((∎ ∷ (prj 0 v ϵ F)) ∷ (¬ (prj 0 v ϵ E))))))
  : π (eql_set E F) ≔
begin
  assume E F h1 h2 a;
  refine ∧ᵢ _ _
  { assume ha;
    refine ¬¬ₑ (a ϵ F) _;
    assume hnf;
    refine !!_to_pi _ h1 (unit ⨾ a) (⋀₂_intro ha hnf) }
  { assume hf;
    refine ¬¬ₑ (a ϵ E) _;
    assume hne;
    refine !!_to_pi _ h2 (unit ⨾ a) (⋀₂_intro hf hne) }
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

// ---- `_1` (Result-form) variants — §8.13 ----
//
// EVR1/4/11, EAXM1/2, ECTR1–6: Schema 0 leaves; res_tm = ⊤.
// EVR2, EVR3: Schema 1 with specific equality bridges (¬=_idem, evr3_eq).
// EAXM31, EAXM32, EIMP51, EIMP52, EAXM91, EAXM92, EQC1, EQC2, EQS1,
// EQS2: Schema 1 passthrough.
// OPR1, OPR2: Schema 1 via the opr1_eq / opr2_eq bridges.

// EVR1: ¬(E=E) ⇒ P ≡ ⊥ ⇒ P ≡ ⊤ — ¬(E=E) is absurd (eq_refl), vacuously ⊤.
symbol EVR1_1 [E : τ ι] [P : Prop] : Res (¬ (E = E) ⇒ P)
  ≔ mk_0 (prop_eq_top EVR1);

// EVR2: Schema 1 — passthrough through stdlib's `¬=_idem`.
symbol EVR2_1 [E : τ ι]
  (r : Res ⊥) : Res (¬ (E = E))
  ≔ mk_1 (res_tm r) (eq_trans (¬=_idem ι E) (res_eq r));

// EVR3: Schema 1 — passthrough via the `evr3_eq` bridge.
symbol EVR3_1 [E : τ ι] [P : Prop]
  (r : Res P) : Res ((E = E) ⇒ P)
  ≔ mk_1 (res_tm r) (eq_trans evr3_eq (res_eq r));

// EVR4: trivial — `E = E = ⊤` via stdlib's `=_idem`.
symbol EVR4_1 [E : τ ι] : Res (E = E) ≔ mk_0 (=_idem ι E);

// EVR11: numeric ≠ — the antecedent n = m is absurd (n, m distinct literals),
// so the implication is vacuously ⊤.  Takes that disequality as evidence.
symbol EVR11_1 [n m : τ ι] [P : Prop] (h : π (¬ (n = m)))
  : Res ((n = m) ⇒ P) ≔ mk_0 (prop_eq_top (λ heq, ⊥ₑ (h heq)));

// EAXM1/EAXM2: hyp-driven contradictions, leaf form (Schema 0, reuse base).
symbol EAXM1_1 [E F : τ ι] [P : Prop] (h : π (¬ (F = E)))
  : Res ((E = F) ⇒ P) ≔ mk_0 (prop_eq_top (EAXM1 h));
symbol EAXM2_1 [E F : τ ι] [P : Prop] (h : π (F = E))
  : Res (¬ (E = F) ⇒ P) ≔ mk_0 (prop_eq_top (EAXM2 h));

// EAXM31/EAXM32: Schema 1 passthrough through eq commutativity.
symbol EAXM31_1 [E F : τ ι]
  (r : Res (F = E)) : Res (E = F)
  ≔ mk_1 (res_tm r) (eq_trans (eq_comm_prop E F) (res_eq r));

symbol EAXM32_1 [E F : τ ι]
  (r : Res (¬ (F = E))) : Res (¬ (E = F))
  ≔ mk_1 (res_tm r) (eq_trans (not_cong (eq_comm_prop E F)) (res_eq r));

// EIMP51/EIMP52: Schema 1 — strip the known (dis)equality antecedent
// (imp_known_drop), the equality supplied as evidence.
symbol EIMP51_1 [E F : τ ι] [P : Prop] (h : π (¬ (E = F)))
  (r : Res P) : Res (¬ (E = F) ⇒ P)
  ≔ mk_1 (res_tm r) (eq_trans (imp_known_drop h) (res_eq r));

symbol EIMP52_1 [E F : τ ι] [P : Prop] (h : π (E = F))
  (r : Res P) : Res ((E = F) ⇒ P)
  ≔ mk_1 (res_tm r) (eq_trans (imp_known_drop h) (res_eq r));

// EAXM91/EAXM92: Schema 1 — strip the instantiation (dis)equality (known from
// the universal hyp), supplied as evidence.
symbol EAXM91_1 [n] [p q : Tuple n → τ ι] (v : Tuple n) [Q : Prop]
  (h : π (q v = p v)) (r : Res Q) : Res ((q v = p v) ⇒ Q)
  ≔ mk_1 (res_tm r) (eq_trans (imp_known_drop h) (res_eq r));

symbol EAXM92_1 [n] [p q : Tuple n → τ ι] (v : Tuple n) [Q : Prop]
  (h : π (¬ (q v = p v))) (r : Res Q) : Res (¬ (q v = p v) ⇒ Q)
  ≔ mk_1 (res_tm r) (eq_trans (imp_known_drop h) (res_eq r));

// OPR1_1: Schema 1 via the opr1_eq bridge.
symbol OPR1_1 [E : τ ι] (P : τ ι → Prop) [x : τ ι]
  (r : Res (x = E ⇒ P E)) : Res (x = E ⇒ P x)
  ≔ mk_1 (res_tm r) (eq_trans (opr1_eq P x) (res_eq r));

// OPR2_1: Schema 1 via the opr2_eq bridge.
symbol OPR2_1 [E : τ ι] (P : τ ι → Prop) [x : τ ι]
  (r : Res (E = x ⇒ P E)) : Res (E = x ⇒ P x)
  ≔ mk_1 (res_tm r) (eq_trans (opr2_eq P x) (res_eq r));

// EQC1/EQC2: pair-equality decomposition, Schema 1 passthrough (pair_inj).
symbol EQC1_1 [a b c d : τ ι] [P : Prop]
  (r : Res ((¬ (a = c) ∨ ¬ (b = d)) ⇒ P))
  : Res (¬ ((a ↦ b) = (c ↦ d)) ⇒ P)
  ≔ mk_1 (res_tm r)
       (eq_trans (imp_cong_l (eq_trans (not_cong pair_eq_decomp)
                                       (deMorgan_∧ (a = c) (b = d))))
                 (res_eq r));

symbol EQC2_1 [a b c d : τ ι] [P : Prop]
  (r : Res (⋀ (∎ ∷ (a = c) ∷ (b = d)) ⇒ P))
  : Res (((a ↦ b) = (c ↦ d)) ⇒ P)
  ≔ mk_1 (res_tm r)
       (eq_trans (imp_cong_l (eq_trans pair_eq_decomp (eq_sym conj2_eq)))
                 (res_eq r));

// EQS1/EQS2: set-equality lifting, Schema 1 passthrough (eql_set_eq).
symbol EQS1_1 [E F : τ ι] [R : Prop]
  (r : Res ((E = F) ⇒ R)) : Res (eql_set E F ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (imp_cong_l eql_set_eq) (res_eq r));

symbol EQS2_1 [E F : τ ι] [R : Prop]
  (r : Res (¬ (E = F) ⇒ R)) : Res (¬ eql_set E F ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (imp_cong_l (not_cong eql_set_eq)) (res_eq r));

// ECTR1–6: hyp-driven contradictions, Schema 0 leaves (reuse base + prop_eq_top).
symbol ECTR1_1 [E F : τ ι] (Q : τ ι → Prop) [P : Prop]
  (h1 : π (¬ (Q E))) (h2 : π (Q F)) : Res ((E = F) ⇒ P)
  ≔ mk_0 (prop_eq_top (ECTR1 Q h1 h2));

symbol ECTR2_1 [E F : τ ι] (Q : τ ι → Prop) [P : Prop]
  (h1 : π (¬ (Q E))) (h2 : π (Q F)) : Res ((F = E) ⇒ P)
  ≔ mk_0 (prop_eq_top (ECTR2 Q h1 h2));

symbol ECTR3_1 [E F : τ ι] (P : τ ι → Prop) [Q : Prop]
  (h1 : π (E = F)) (h2 : π (P F)) : Res (¬ (P E) ⇒ Q)
  ≔ mk_0 (prop_eq_top (ECTR3 P h1 h2));

symbol ECTR4_1 [E F : τ ι] (P : τ ι → Prop) [Q : Prop]
  (h1 : π (F = E)) (h2 : π (P F)) : Res (¬ (P E) ⇒ Q)
  ≔ mk_0 (prop_eq_top (ECTR4 P h1 h2));

symbol ECTR5_1 [E F : τ ι] (P : τ ι → Prop) [Q : Prop]
  (h1 : π (E = F)) (h2 : π (¬ (P F))) : Res ((P E) ⇒ Q)
  ≔ mk_0 (prop_eq_top (ECTR5 P h1 h2));

symbol ECTR6_1 [E F : τ ι] (P : τ ι → Prop) [Q : Prop]
  (h1 : π (F = E)) (h2 : π (¬ (P F))) : Res ((P E) ⇒ Q)
  ≔ mk_0 (prop_eq_top (ECTR6 P h1 h2));
