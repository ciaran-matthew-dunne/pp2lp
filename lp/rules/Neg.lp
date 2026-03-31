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

// ---- Primed variants (equality-based) ----

// NOT1_1: pass-through, computes ¬¬P⇒R = P⇒R.
opaque symbol NOT1_1 [P R S : Prop]
  : π ((P ⇒ R) = S)
  → π ((¬ ¬ P ⇒ R) = S) ≔
begin
  assume P R S h;
  have eq : π ((¬ ¬ P ⇒ R) = (P ⇒ R))
    { refine propExt _ _ _ _
      { assume h1 hp; refine h1 (λ hnp, hnp hp) }
      { assume h1 hnnp; refine h1 (¬¬ₑ P hnnp) } };
  rewrite eq; refine h
end;

// NOT2_1: pass-through, computes ¬¬P = P.
opaque symbol NOT2_1 [P S : Prop]
  : π (P = S)
  → π (¬ ¬ P = S) ≔
begin
  assume P S h; rewrite ¬¬ₑ_eq; refine h
end;
