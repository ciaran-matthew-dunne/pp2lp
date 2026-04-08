// Negation (§A.5) — shallow encoding
require open pp2lp.B;

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
