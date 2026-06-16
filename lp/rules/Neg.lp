// Negation (§A.5) — shallow encoding
require open pp2lp.B pp2lp.Int pp2lp.Quant pp2lp.rules.Res;

// NOT1: H ⊢ P ⇒ R → H ⊢ ¬¬P ⇒ R
opaque symbol NOT1 [P R]
  : π (P ⇒ R)
  → π (¬ ¬ P ⇒ R) ≔
begin
  assume P R h1 h2;
  refine h1 (¬¬ₑ P h2)
end;

// NOT2: H ⊢ P → H ⊢ ¬¬P
opaque symbol NOT2 [P]
  : π P
  → π (¬ ¬ P) ≔
begin
  assume P h1 h2;
  refine h2 h1
end;

// ---- `_1` (Result-form) variants — §8.13 ----

// NOT1_1: Schema 1 — passthrough.
symbol NOT1_1 [P R : Prop]
  (r : Res (P ⇒ R)) : Res (¬ ¬ P ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans not1_eq (res_eq r));

// NOT2_1: Schema 1 — passthrough via stdlib's `¬¬ₑ_eq`.
symbol NOT2_1 [P : Prop]
  (r : Res P) : Res (¬ ¬ P)
  ≔ mk_1 (res_tm r) (eq_trans (¬¬ₑ_eq P) (res_eq r));
