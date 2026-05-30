// Disjunction (§A.2) — shallow encoding
require open pp2lp.B pp2lp.Quant pp2lp.rules.Res;

// ---- Base rules ----

// OR1: H ⊢ ¬P ⇒ (¬Q ⇒ R) → H ⊢ ¬(P ∨ Q) ⇒ R
opaque symbol OR1 [P Q R]
  : π (¬ P ⇒ (¬ Q ⇒ R))
  → π (¬ (P ∨ Q) ⇒ R) ≔
begin
  assume P Q R h1 h2;
  have h : π (¬ P ∧ ¬ Q) {refine =⇒ (deMorgan_∨ P Q) h2};
  refine h1 (∧ₑ₁ h) (∧ₑ₂ h)
end;

// OR2: H ⊢ ¬Q; H ⊢ ¬P → H ⊢ ¬(P ∨ Q)
opaque symbol OR2 [P Q]
  : π (¬ Q)
  → π (¬ P)
  → π (¬ (P ∨ Q)) ≔
begin
  assume P Q hq hp hpq;
  refine ∨ₑ hpq _ _ {
    assume h; refine hp h
  } {
    assume h; refine hq h
  }
end;

// OR3: H ⊢ Q ⇒ R; H ⊢ P ⇒ R → H ⊢ (P ∨ Q) ⇒ R
opaque symbol OR3 [P Q R]
  : π (Q ⇒ R)
  → π (P ⇒ R)
  → π ((P ∨ Q) ⇒ R) ≔
begin
  assume P Q R hq hp hpq;
  refine ∨ₑ hpq _ _ {
    assume h; refine hp h
  } {
    assume h; refine hq h
  }
end;

// OR4: H ⊢ ¬P ⇒ Q → H ⊢ P ∨ Q
opaque symbol OR4 [P Q]
  : π (¬ P ⇒ Q)
  → π (P ∨ Q) ≔
begin
  assume P Q h1;
  refine ∨ₑ (em P) _ _ {
    assume hp; refine ∨ᵢ₁ hp
  } {
    assume hnp; refine ∨ᵢ₂ (h1 hnp)
  }
end;

// ---- `_1` (Result-form) variants — §8.13 ----

// OR1_1: Schema 1 — passthrough.
symbol OR1_1 [P Q R : Prop]
  (r : Res (¬ P ⇒ ¬ Q ⇒ R)) : Res (¬ (P ∨ Q) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans or1_eq (res_eq r));

// OR2_1: Schema 2 — combine.
symbol OR2_1 [P Q : Prop]
  (r1 : Res (¬ Q)) (r2 : Res (¬ P)) : Res (¬ (P ∨ Q))
  ≔ mk_res (concat (res_ts r1) (res_ts r2))
      (eq_trans or2_eq
        (eq_trans (conj_eq (res_eq r1) (res_eq r2))
                  (conj_concat_eq (res_ts r1) (res_ts r2))));

// OR3_1: Schema 2 — combine.
symbol OR3_1 [P Q R : Prop]
  (r1 : Res (Q ⇒ R)) (r2 : Res (P ⇒ R))
  : Res ((P ∨ Q) ⇒ R)
  ≔ mk_res (concat (res_ts r1) (res_ts r2))
      (eq_trans or3_eq
        (eq_trans (conj_eq (res_eq r1) (res_eq r2))
                  (conj_concat_eq (res_ts r1) (res_ts r2))));

// OR4_1: Schema 1 — passthrough.
symbol OR4_1 [P Q : Prop]
  (r : Res (¬ P ⇒ Q)) : Res (P ∨ Q)
  ≔ mk_1 (res_tm r) (eq_trans (or4_eq P Q) (res_eq r));
