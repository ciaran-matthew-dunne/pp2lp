// Implication (§A.3) — shallow encoding
require open pp2lp.B pp2lp.lemmas.Int pp2lp.lemmas.ConjList pp2lp.lemmas.Tuple pp2lp.rules.Res;

// ---- Base rules ----

// IMP1: H ⊢ P ⇒ (¬Q ⇒ R) → H ⊢ ¬(P ⇒ Q) ⇒ R
opaque symbol IMP1 [P Q R]
  : π (P ⇒ (¬ Q ⇒ R))
  → π (¬ (P ⇒ Q) ⇒ R) ≔
begin
  assume P Q R h1 h2;
  have hp : π P {
    refine ¬¬ₑ P _;
    assume hnp;
    refine h2 (λ p, ⊥ₑ (hnp p))
  };
  have hnq : π (¬ Q) {
    assume hq;
    refine h2 (λ _, hq)
  };
  refine h1 hp hnq
end;

// IMP2: H ⊢ ¬Q; H ⊢ P → H ⊢ ¬(P ⇒ Q)
opaque symbol IMP2 [P Q]
  : π (¬ Q)
  → π P
  → π (¬ (P ⇒ Q)) ≔
begin
  assume P Q hnq hp hpq;
  refine hnq (hpq hp)
end;

// IMP3: H ⊢ Q ⇒ R; H ⊢ ¬P ⇒ R → H ⊢ (P ⇒ Q) ⇒ R
opaque symbol IMP3 [P Q R]
  : π (Q ⇒ R)
  → π (¬ P ⇒ R)
  → π ((P ⇒ Q) ⇒ R) ≔
begin
  assume P Q R hqr hnpr hpq;
  refine ∨ₑ (em P) _ _ {
    assume hp; refine hqr (hpq hp)
  } {
    assume hnp; refine hnpr hnp
  }
end;

// IMP4: H, P ⊢ Q → H ⊢ P ⇒ Q
opaque symbol IMP4 [P Q]
  : (π P → π Q)
  → π (P ⇒ Q) ≔
begin
  assume P Q h; refine h
end;

// IMP5: P is in H; H ⊢ Q → H ⊢ P ⇒ Q
opaque symbol IMP5 [P Q]
  : π Q
  → π (P ⇒ Q) ≔
begin
  assume P Q hq hp; refine hq
end;

// ---- `_1` (Result-form) variants — §8.13 ----

// IMP1_1: Schema 1 — passthrough.  Preserve the child's ⋀-list (`mk_res (res_ts r)`
// rather than collapsing to the singleton `mk_1 (res_tm r)`): when this result
// feeds an outer IMP3_1/IMP2_1 `concat`, the list must stay flat so a ≥3-conjunct
// cascade body becomes `⋀(∎∷A∷B∷C)`, not `⋀(∎∷A∷(B∧C))` — the latter mis-associates
// the continuation's NRM7 snoc-peel.  `res_tm` is unchanged (singleton-collapse),
// so the proof term and every res_tm-consuming use site are identical.
symbol IMP1_1 [P Q R : Prop]
  (r : Res (P ⇒ ¬ Q ⇒ R)) : Res (¬ (P ⇒ Q) ⇒ R)
  ≔ mk_res (res_ts r) (eq_trans imp1_eq (res_eq r));

// IMP2_1: Schema 2 — combine.
symbol IMP2_1 [P Q : Prop]
  (r1 : Res (¬ Q)) (r2 : Res P) : Res (¬ (P ⇒ Q))
  ≔ mk_res (concat (res_ts r1) (res_ts r2))
      (eq_trans imp2_eq
        (eq_trans (conj_eq (res_eq r1) (res_eq r2))
                  (conj_concat_eq (res_ts r1) (res_ts r2))));

// IMP3_1: Schema 2 — combine.
symbol IMP3_1 [P Q R : Prop]
  (r1 : Res (Q ⇒ R)) (r2 : Res (¬ P ⇒ R))
  : Res ((P ⇒ Q) ⇒ R)
  ≔ mk_res (concat (res_ts r1) (res_ts r2))
      (eq_trans imp3_eq
        (eq_trans (conj_eq (res_eq r1) (res_eq r2))
                  (conj_concat_eq (res_ts r1) (res_ts r2))));

// IMP4_1: special case — result is P ⇒ R (the antecedent prepended to
// the child's result).
symbol IMP4_1 [P Q : Prop]
  (r : Res Q) : Res (P ⇒ Q)
  ≔ mk_1 (P ⇒ res_tm r) (imp_cong_r (res_eq r));

// IMP4_1U: IMP4_1 whose child chain uses the antecedent — PP holds the assumed
// antecedent in its hypothesis store, so a chain-local AXM3_1 discharges a
// conjunct equal to it.  Take the child as the *equality under the hypothesis*
// `π P → π (Q = R)`; `imp_cong_r_under` lifts it to the unconditional
// implication equality.  R (the child's result) is inferred: it is
// `conj (res_ts (child hp))`, and `res_ts` reduces through the `mk_0`/`concat`
// structure without touching `hp`, so it closes to a hypothesis-free formula.
symbol IMP4_1U [P Q R : Prop]
  (f : π P → π (Q = R)) : Res (P ⇒ Q)
  ≔ mk_1 (P ⇒ R) (imp_cong_r_under f);

// IMP5_1: strip a known antecedent (hp : π P) — collapses the ⇒.
symbol IMP5_1 [P Q : Prop]
  (hp : π P) (r : Res Q) : Res (P ⇒ Q)
  ≔ mk_1 (res_tm r) (eq_trans (imp_known_drop hp) (res_eq r));
