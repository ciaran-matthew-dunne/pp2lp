// Existential quantification (§A.8) — tuple-based encoding.
//
// PP traces emit only singleton existentials in practice (prv: every
// `#(x)` is arity-1), but we encode the compound↔nested conversions
// XST1–4 for completeness.
//
// As with ALL1–4, we read `(x,y)` in the spec as "n-tuple x + 1-tuple
// y", so the rule peels one variable at a time. Unlike `!!`, `??` is
// a defined symbol that reduces to nested ∃, so the compound and
// nested forms are *definitionally equal* — XST1–4 are identity in
// HOAS.

require open pp2lp.B pp2lp.Quant;

// Helper: compound → nested for `??`. Defined by rewrite rule on
// the tuple constructor; pattern-match exposes (w ⨾ a) shape.
symbol compound_to_nested_∃ [n] (P : Tuple (+1 n) → Prop)
  : Π v : Tuple (+1 n), π (P v)
  → π (`?? w : Tuple n, `?? y : Tuple 1, P (w ⨾ prj 0 y));
rule compound_to_nested_∃ [$n] $P ($w ⨾ $a) $h ↪
  pi_to_??_intro (λ w', `?? y : Tuple 1, $P (w' ⨾ prj 0 y))
                 $w
                 (pi_to_??_intro (λ y, $P ($w ⨾ prj 0 y))
                                 (unit ⨾ $a) $h);

// Helper: nested → compound for `??`.
opaque symbol nested_to_compound_∃ [n] (P : Tuple (+1 n) → Prop)
  : π (`?? w : Tuple n, `?? y : Tuple 1, P (w ⨾ prj 0 y))
  → π (`?? v : Tuple (+1 n), P v) ≔
begin
  assume n P h;
  refine pi_to_??_elim
    (λ w : Tuple n, `?? y : Tuple 1, P (w ⨾ prj 0 y))
    _ h;
  assume w hw;
  refine pi_to_??_elim (λ y : Tuple 1, P (w ⨾ prj 0 y)) _ hw;
  assume y hy;
  refine pi_to_??_intro P (w ⨾ prj 0 y) hy
end;

// XST1: H ⊢ ¬(∃(x,y)·P) ⇒ R → H ⊢ ¬(∃x·∃y·P) ⇒ R
opaque symbol XST1 [n] [P : Tuple (+1 n) → Prop] [R : Prop]
  : π (¬ (`?? v : Tuple (+1 n), P v) ⇒ R)
  → π (¬ (`?? w : Tuple n, `?? y : Tuple 1, P (w ⨾ prj 0 y)) ⇒ R) ≔
begin
  assume n P R h hnnested;
  refine h _;
  assume hcompound;
  refine hnnested _;
  refine pi_to_??_elim P _ hcompound;
  assume v hv;
  refine compound_to_nested_∃ P v hv
end;

// XST2: H ⊢ ¬(∃(x,y)·P) → H ⊢ ¬(∃x·∃y·P)
opaque symbol XST2 [n] [P : Tuple (+1 n) → Prop]
  : π (¬ (`?? v : Tuple (+1 n), P v))
  → π (¬ (`?? w : Tuple n, `?? y : Tuple 1, P (w ⨾ prj 0 y))) ≔
begin
  assume n P h hnested;
  refine h (nested_to_compound_∃ P hnested)
end;

// XST3: H ⊢ (∃(x,y)·P) ⇒ R → H ⊢ (∃x·∃y·P) ⇒ R
opaque symbol XST3 [n] [P : Tuple (+1 n) → Prop] [R : Prop]
  : π ((`?? v : Tuple (+1 n), P v) ⇒ R)
  → π ((`?? w : Tuple n, `?? y : Tuple 1, P (w ⨾ prj 0 y)) ⇒ R) ≔
begin
  assume n P R h hnested;
  refine h (nested_to_compound_∃ P hnested)
end;

// XST4: H ⊢ ∃(x,y)·P → H ⊢ ∃x·∃y·P
opaque symbol XST4 [n] [P : Tuple (+1 n) → Prop]
  : π (`?? v : Tuple (+1 n), P v)
  → π (`?? w : Tuple n, `?? y : Tuple 1, P (w ⨾ prj 0 y)) ≔
begin
  assume n P h;
  refine pi_to_??_elim P _ h;
  assume v hv;
  refine compound_to_nested_∃ P v hv
end;

// ---- Negative side: ¬(∃ …) ⇒ R / ¬(∃ …) ----------------------

// XST5: H ⊢ (∀-block, ¬P) ⇒ R → H ⊢ ¬(∃-block, P) ⇒ R

opaque symbol XST5 [n] [P : Tuple n → Prop] [R : Prop]
  : π ((`!! v, ¬ (P v)) ⇒ R)
  → π (¬ (`?? v, P v) ⇒ R) ≔
begin
  assume n P R h1 h2;
  refine h1 (pi_to_!! (λ v, ¬ (P v))
    (λ v hpv, h2 (pi_to_??_intro P v hpv)))
end;

// XST51: H ⊢ (∀-block, P) ⇒ R → H ⊢ ¬(∃-block, ¬P) ⇒ R

opaque symbol XST51 [n] [P : Tuple n → Prop] [R : Prop]
  : π ((`!! v, P v) ⇒ R)
  → π (¬ (`?? v, ¬ (P v)) ⇒ R) ≔
begin
  assume n P R h1 h2;
  refine h1 (pi_to_!! P (λ v,
    ¬¬ₑ (P v) (λ hnpv, h2 (pi_to_??_intro (λ v, ¬ (P v)) v hnpv))))
end;

// XST6: H ⊢ ∀-block, ¬P → H ⊢ ¬(∃-block, P)

opaque symbol XST6 [n] [P : Tuple n → Prop]
  : π (`!! v, ¬ (P v))
  → π (¬ (`?? v, P v)) ≔
begin
  assume n P h1 h2;
  refine pi_to_??_elim P
    (λ v hpv, !!_to_pi (λ v, ¬ (P v)) h1 v hpv) h2
end;

// XST61: H ⊢ ∀-block, P → H ⊢ ¬(∃-block, ¬P)

opaque symbol XST61 [n] [P : Tuple n → Prop]
  : π (`!! v, P v)
  → π (¬ (`?? v, ¬ (P v))) ≔
begin
  assume n P h1 h2;
  refine pi_to_??_elim (λ v, ¬ (P v))
    (λ v hnpv, hnpv (!!_to_pi P h1 v)) h2
end;

// ---- Positive side: ∃ … ⇒ R / ∃ … ----------------------------

// XST7: H ⊢ ∀-block, P ⇒ R → H ⊢ (∃-block, P) ⇒ R
// "x not free in R" means R : Prop.

opaque symbol XST7 [n] [P : Tuple n → Prop] [R : Prop]
  : π (`!! v, P v ⇒ R)
  → π ((`?? v, P v) ⇒ R) ≔
begin
  assume n P R h1 h2;
  refine pi_to_??_elim P
    (λ v hPv, !!_to_pi (λ v, P v ⇒ R) h1 v hPv) h2
end;

// XST8: result-based ∃-introduction.
//   premise 1: per-tuple Res chain ρ producing res_tm (ρ v) for each v
//              (where each ρ v normalises ¬(P v) to res_tm (ρ v))
//   premise 2: ((`!! v, res_tm (ρ v)) ⇒ ⊥)
//   conclusion: (`?? v, P v)

opaque symbol XST8 [n] [P : Tuple n → Prop]
  (ρ : Π v : Tuple n, Res (¬ (P v)))
  : π ((`!! v, res_tm (ρ v)) ⇒ ⊥) → π (`?? v, P v) ≔
begin
  assume n P ρ h_after;
  refine ¬¬ₑ (`?? v, P v) _;
  assume hne;
  refine h_after (pi_to_!! (λ v, res_tm (ρ v)) (λ v,
    =⇒ (res_eq (ρ v))
       (λ hpv, hne (pi_to_??_intro P v hpv))))
end;
