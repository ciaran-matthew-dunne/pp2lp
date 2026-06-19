// Existential quantification (§A.8) — tuple-based encoding.
//
// PP traces emit only singleton existentials in practice (prv: every
// `#(x)` is arity-1), but we encode the compound↔nested conversions
// XST1–4 for completeness.
//
// As with ALL1–4 (All.lp) these are now CURRIED: P : Tuple n → Tuple 1 → Prop,
// nested conclusion `?? w, ?? y, P w y` (P at a pattern position → `refine XSTn _`
// infers P), compound premise `?? v : Tuple (n ++ 1), P (take v) (drop v)`.  The
// two forms are equal (`??_split_eq`, lemmas/Tuple.lp), so each rule is a one-line
// transport.  Replaces the previous compound-`P (w ⨾ prj 0 y)` encoding (P
// non-pattern, so unemittable) and its `compound_to_nested_∃`/`nested_to_compound_∃`
// helpers.

require open pp2lp.B pp2lp.lemmas.Int pp2lp.lemmas.Tuple pp2lp.rules.Res;

// XST1: H ⊢ ¬(∃(x,y)·P) ⇒ R → H ⊢ ¬(∃x·∃y·P) ⇒ R
opaque symbol XST1 [n] [P : Tuple n → Tuple 1 → Prop] [R : Prop]
  : π (¬ (`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)) ⇒ R)
  → π (¬ (`?? w : Tuple n, `?? y : Tuple 1, P w y) ⇒ R) ≔
begin
  assume n P R h;
  refine =⇒ (imp_cong_l (not_cong (??_split_eq P))) h
end;

// XST2: H ⊢ ¬(∃(x,y)·P) → H ⊢ ¬(∃x·∃y·P)
opaque symbol XST2 [n] [P : Tuple n → Tuple 1 → Prop]
  : π (¬ (`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)))
  → π (¬ (`?? w : Tuple n, `?? y : Tuple 1, P w y)) ≔
begin
  assume n P h;
  refine =⇒ (not_cong (??_split_eq P)) h
end;

// XST3: H ⊢ (∃(x,y)·P) ⇒ R → H ⊢ (∃x·∃y·P) ⇒ R  (existential mirror of ALL3)
opaque symbol XST3 [n] [P : Tuple n → Tuple 1 → Prop] [R : Prop]
  : π ((`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)) ⇒ R)
  → π ((`?? w : Tuple n, `?? y : Tuple 1, P w y) ⇒ R) ≔
begin
  assume n P R h;
  refine =⇒ (imp_cong_l (??_split_eq P)) h
end;

// XST4: H ⊢ ∃(x,y)·P → H ⊢ ∃x·∃y·P
opaque symbol XST4 [n] [P : Tuple n → Tuple 1 → Prop]
  : π (`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v))
  → π (`?? w : Tuple n, `?? y : Tuple 1, P w y) ≔
begin
  assume n P h;
  refine =⇒ (??_split_eq P) h
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
// XST1_1–XST4_1 are the Res-chain forms of the §A.8 existential regroupement.  PP
// emits them PRIMED inside a result chain (`[XST4_1]`, …), where flatten_binds
// cannot reach (the merged binder is born inside `res_tm`).  Each transports the
// curried base rule's compound↔nested equality (`??_split_eq`, lemmas/Tuple.lp)
// through the Schema-1 result bridge — trust-free.  (They replace the trust-bodied
// placeholders deleted 2026-06-12, now that the base rules are curried.)
// XST5–XST6 and XST51/XST61: Schema 1 passthrough.
// XST7_1: Schema 1 via the `xst7_eq` bridge.
// XST8_1: special — chain-shaped, see below.

// XST1_1: chain form of XST1 (¬(∃-merge) ⇒ R).
symbol XST1_1 [n] [P : Tuple n → Tuple 1 → Prop] [R : Prop]
  (r : Res (¬ (`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)) ⇒ R))
  : Res (¬ (`?? w : Tuple n, `?? y : Tuple 1, P w y) ⇒ R)
  ≔ mk_1 (res_tm r)
      (eq_trans (eq_sym (imp_cong_l (not_cong (??_split_eq P)))) (res_eq r));

// XST2_1: chain form of XST2 (¬(∃-merge)).
symbol XST2_1 [n] [P : Tuple n → Tuple 1 → Prop]
  (r : Res (¬ (`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v))))
  : Res (¬ (`?? w : Tuple n, `?? y : Tuple 1, P w y))
  ≔ mk_1 (res_tm r) (eq_trans (eq_sym (not_cong (??_split_eq P))) (res_eq r));

// XST3_1: chain form of XST3 ((∃-merge) ⇒ R).
symbol XST3_1 [n] [P : Tuple n → Tuple 1 → Prop] [R : Prop]
  (r : Res ((`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)) ⇒ R))
  : Res ((`?? w : Tuple n, `?? y : Tuple 1, P w y) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (eq_sym (imp_cong_l (??_split_eq P))) (res_eq r));

// XST4_1: chain form of XST4 (∃-merge).
symbol XST4_1 [n] [P : Tuple n → Tuple 1 → Prop]
  (r : Res (`?? v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)))
  : Res (`?? w : Tuple n, `?? y : Tuple 1, P w y)
  ≔ mk_1 (res_tm r) (eq_trans (eq_sym (??_split_eq P)) (res_eq r));

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
