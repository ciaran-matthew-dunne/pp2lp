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

require open pp2lp.B pp2lp.Quant pp2lp.rules.Res;

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

// ---- `_1` (Result-form) variants — §8.13 ----
//
// XST1–4 are the chain form of the existential regroupement
// `∃x·∃y·P ↦ ∃(x,y)·P` (§A.8) — NOT a HOAS identity.  As with ALL1–4 (All.lp) the
// merge is done at the AST level by `flatten_binds` (the `binder_merge` skip in
// rule_db.ml), so they are never emitted and the `res_tm` bridge is left as
// `trust`.  Eliminable via the `??`-currying equality (propExt over
// compound_to_nested_∃ / nested_to_compound_∃) if a merge ever needs emitting in
// a Res chain.
// XST5–XST6 and XST51/XST61: Schema 1 passthrough.
// XST7_1: Schema 1 via the `xst7_eq` bridge.
// XST8_1: special — chain-shaped, see below.

symbol XST1_1 [n] [P : Tuple (+1 n) → Prop] [R : Prop]
  (r : Res (¬ (`?? v : Tuple (+1 n), P v) ⇒ R))
  : Res (¬ (`?? w : Tuple n, `?? y : Tuple 1, P (w ⨾ prj 0 y)) ⇒ R)
  ≔ mk_1 (res_tm r) trust;

symbol XST2_1 [n] [P : Tuple (+1 n) → Prop]
  (r : Res (¬ (`?? v : Tuple (+1 n), P v)))
  : Res (¬ (`?? w : Tuple n, `?? y : Tuple 1, P (w ⨾ prj 0 y)))
  ≔ mk_1 (res_tm r) trust;

symbol XST3_1 [n] [P : Tuple (+1 n) → Prop] [R : Prop]
  (r : Res ((`?? v : Tuple (+1 n), P v) ⇒ R))
  : Res ((`?? w : Tuple n, `?? y : Tuple 1, P (w ⨾ prj 0 y)) ⇒ R)
  ≔ mk_1 (res_tm r) trust;

symbol XST4_1 [n] [P : Tuple (+1 n) → Prop]
  (r : Res (`?? v : Tuple (+1 n), P v))
  : Res (`?? w : Tuple n, `?? y : Tuple 1, P (w ⨾ prj 0 y))
  ≔ mk_1 (res_tm r) trust;

symbol XST5_1 [n] [P : Tuple n → Prop] [R : Prop]
  (r : Res ((`!! v, ¬ (P v)) ⇒ R))
  : Res (¬ (`?? v, P v) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (imp_cong_l xst6_eq) (res_eq r));

symbol XST51_1 [n] [P : Tuple n → Prop] [R : Prop]
  (r : Res ((`!! v, P v) ⇒ R))
  : Res (¬ (`?? v, ¬ (P v)) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (imp_cong_l xst61_eq) (res_eq r));

symbol XST6_1 [n] [P : Tuple n → Prop]
  (r : Res (`!! v, ¬ (P v)))
  : Res (¬ (`?? v, P v))
  ≔ mk_1 (res_tm r) (eq_trans xst6_eq (res_eq r));

symbol XST61_1 [n] [P : Tuple n → Prop]
  (r : Res (`!! v, P v))
  : Res (¬ (`?? v, ¬ (P v)))
  ≔ mk_1 (res_tm r) (eq_trans xst61_eq (res_eq r));

// XST7_1: (∃-block, P) ⇒ R via (∀-block, P ⇒ R).
symbol XST7_1 [n] [P : Tuple n → Prop] [R : Prop]
  (r : Res (`!! v, P v ⇒ R)) : Res ((`?? v, P v) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans xst7_eq (res_eq r));

// XST8_1 (XST8'): result-form ∃-introduction, mirroring XST8 (cf. ALL7_1).
// Per-tuple Res chain ρ (normalising ¬(P v)) + continuation r packaging
// ((`!! v, res_tm (ρ v)) ⇒ ⊥).  The chain emitter supplies ρ under the
// bound v, so ρ is non-trivial in general (not the identity the old
// 1-argument form assumed).
symbol XST8_1 [n] [P : Tuple n → Prop]
  (ρ : Π v : Tuple n, Res (¬ (P v)))
  (r : Res ((`!! v, res_tm (ρ v)) ⇒ ⊥)) : Res (`?? v, P v) ≔
begin
  assume n P ρ r;
  refine mk_1 (res_tm r) _;
  have h1 : π ((`?? v, P v) = ((`!! v, res_tm (ρ v)) ⇒ ⊥))
    { refine eq_trans (@xst8_eq n P) (imp_cong_l (!!_cong (λ v, res_eq (ρ v)))) };
  refine eq_trans h1 (res_eq r)
end;
