// Universal quantification (§A.7) — tuple-based encoding.
//
// Compound bindings in PP traces map to `!! v : Tuple n, P v`. The
// per-arity scaffolding the previous version of this file carried
// (ALL5_2, ALL7_2, ALL7_3, ALL7_2i, ALL7_3i, …) is gone: the uniform
// tuple-indexed forms below subsume every arity.
//
// ALL1–4 are compound↔nested conversions (§A.7 regroupement).  All four are now
// CURRIED, like ALL3: P : Tuple n → Tuple 1 → Prop, so the nested conclusion is
//
//   nested   : `!! w : Tuple n, `!! y : Tuple 1, P w y
//
// where `P w y` is a *pattern* (P applied to the distinct bound tuples) — hence
// `refine ALLn _` infers P, no explicit predicate.  The compound premise splits
// v : Tuple (n ++ 1) with take/drop:
//
//   compound : `!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)
//
// The two forms are equal (`!!_split_eq`, lemmas/Tuple.lp, proved once by propExt
// over reconstruction `tcat` + projection `take`/`drop`), so ALL1/2/4 are one-line
// transports of it; ALL3 keeps its direct projection proof.  Replaces the previous
// compound-`P (w ⨾ prj 0 y)` encoding (non-pattern, so unemittable).

require open pp2lp.B pp2lp.lemmas.Int pp2lp.lemmas.Tuple pp2lp.rules.Res;

// ALL1: H ⊢ ¬(∀(x,y)·P) ⇒ R → H ⊢ ¬(∀x·∀y·P) ⇒ R
opaque symbol ALL1 [n] [P : Tuple n → Tuple 1 → Prop] [R : Prop]
  : π (¬ (`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)) ⇒ R)
  → π (¬ (`!! w : Tuple n, `!! y : Tuple 1, P w y) ⇒ R) ≔
begin
  assume n P R h;
  refine =⇒ (imp_cong_l (not_cong (!!_split_eq P))) h
end;

// ALL2: H ⊢ ¬(∀(x,y)·P) → H ⊢ ¬(∀x·∀y·P)
opaque symbol ALL2 [n] [P : Tuple n → Tuple 1 → Prop]
  : π (¬ (`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)))
  → π (¬ (`!! w : Tuple n, `!! y : Tuple 1, P w y)) ≔
begin
  assume n P h;
  refine =⇒ (not_cong (!!_split_eq P)) h
end;

// ALL3: H ⊢ (∀(x,y)·P) ⇒ R → H ⊢ (∀x·∀y·P) ⇒ R   (§A.7 regroupement)
//
// Curried encoding: P : Tuple n → Tuple 1 → Prop, so the nested conclusion is
// `!! w, !! y, P w y` — P sits at a *pattern* position (applied to the distinct
// bound tuples w, y), hence the emitter need not pass it explicitly: `refine
// ALL3 _` infers it from the goal.  The compound premise splits v with
// take/drop, whose prj-commute rules reduce `P (take v) (drop v)` to the
// renderer's slot order (first PP var ↦ prj 0, the trailing var ↦ prj n).  That
// slot order is exactly what the old `ALL3R` variant was hand-rolling, so ALL3R
// is gone — take/drop subsume it.
opaque symbol ALL3 [n] [P : Tuple n → Tuple 1 → Prop] [R : Prop]
  : π ((`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)) ⇒ R)
  → π ((`!! w : Tuple n, `!! y : Tuple 1, P w y) ⇒ R) ≔
begin
  assume n P R h hn;
  refine h _;
  refine pi_to_!! _ _; assume v;
  refine !!_to_pi (λ y, P (take [n] [1] v) y)
           (!!_to_pi (λ w, `!! y : Tuple 1, P w y) hn (take [n] [1] v))
           (drop [n] [1] v)
end;

// ALL4: H ⊢ ∀(x,y)·P → H ⊢ ∀x·∀y·P
opaque symbol ALL4 [n] [P : Tuple n → Tuple 1 → Prop]
  : π (`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v))
  → π (`!! w : Tuple n, `!! y : Tuple 1, P w y) ≔
begin
  assume n P h;
  refine =⇒ (!!_split_eq P) h
end;

// ALL5: H ⊢ ∀-block, ¬P ⇒ R → H ⊢ ¬(∀-block, P) ⇒ R
// "x not free in R" means R : Prop (uniform across arities).

opaque symbol ALL5 [n] [P : Tuple n → Prop] [R : Prop]
  : π (`!! v, ¬ (P v) ⇒ R)
  → π (¬ (`!! v, P v) ⇒ R) ≔
begin
  assume n P R h1 h2;
  refine ¬¬ₑ R _;
  assume hnr;
  refine h2 (pi_to_!! P (λ v,
    ¬¬ₑ (P v) (λ hnpv, hnr (!!_to_pi (λ v, ¬ (P v) ⇒ R) h1 v hnpv))))
end;

// ALL6: H ⊢ (∀-block, P) ⇒ ⊥ → H ⊢ ¬(∀-block, P)
// Definitional in HOAS: ¬Q ≡ Q ⇒ ⊥.

opaque symbol ALL6 [n] [P : Tuple n → Prop]
  : π ((`!! v, P v) ⇒ ⊥)
  → π (¬ (`!! v, P v)) ≔
begin assume n P h; refine h end;

// ALL7: result-based form.
//   premise 1: per-tuple Res chain ρ producing res_tm (ρ v) for each v
//   premise 2: ((`♢ v, res_tm (ρ v)) ⇒ Q) (continuation)
//   conclusion: (`!! v, P v) ⇒ Q
//
// Per spec: H ⊢ (♢x · R) ⇒ Q | H ⊢ (∀x · P) ⇒ Q. The continuation
// premise is the "after-normalisation" form, marked ♢; the conclusion
// matches PP's `!`-binder, encoded as `!!`.

opaque symbol ALL7 [n] [P : Tuple n → Prop] [Q : Prop]
  (ρ : Π v : Tuple n, Res (P v))
  : π ((`♢ v, res_tm (ρ v)) ⇒ Q) → π ((`!! v, P v) ⇒ Q) ≔
begin
  assume n P Q ρ h_after h_P;
  refine h_after (pi_to_♢ (λ v, res_tm (ρ v))
    (λ v, =⇒ (res_eq (ρ v)) (!!_to_pi P h_P v)))
end;

// ALL8: H ⊢ P → H ⊢ ∀-block, P
// Universal-introduction. Spec premise is the body P with the bound
// variable free in context; HOAS-encoded as a per-tuple proof family
// (Π v, π (P v)). With `!!` rigid we need `pi_to_!!` to bridge.

opaque symbol ALL8 [n] [P : Tuple n → Prop]
  : (Π v : Tuple n, π (P v)) → π (`!! v, P v)
  ≔ λ f, pi_to_!! _ f;

// ALL9: H, (∀-block, T) ⊢ Q → H ⊢ (♡-block, T) ⇒ Q
// Transport antecedent ♡ → !! via `♡_eq_!!`, then apply h.

opaque symbol ALL9 [n] [T : Tuple n → Prop] [Q : Prop]
  : (π (`!! v, T v) → π Q)
  → π ((`♡ v, T v) ⇒ Q) ≔
begin
  assume n T Q h hheart;
  refine h (=⇒ (♡_eq_!! T) hheart)
end;

// ---- `_1` (Result-form) variants — §8.13 ----
//
// ALL1_1–ALL4_1 are the Res-chain forms of the §A.7 quantifier regroupement.  PP
// emits them PRIMED inside a result chain (`[ALL3_1]`, …), where flatten_binds
// cannot reach — the merged binder is born inside `res_tm`, not in the goal.  Each
// transports the curried base rule's compound↔nested equality (`!!_split_eq`,
// lemmas/Tuple.lp) through the Schema-1 result bridge `mk_1 (res_tm r) (eq_trans
// <concl = prem> (res_eq r))` — trust-free.  (They replace the trust-bodied
// placeholders deleted 2026-06-12, now that the base rules are curried.)

// ALL1_1: chain form of ALL1 (¬(∀-merge) ⇒ R).
symbol ALL1_1 [n] [P : Tuple n → Tuple 1 → Prop] [R : Prop]
  (r : Res (¬ (`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)) ⇒ R))
  : Res (¬ (`!! w : Tuple n, `!! y : Tuple 1, P w y) ⇒ R)
  ≔ mk_1 (res_tm r)
      (eq_trans (eq_sym (imp_cong_l (not_cong (!!_split_eq P)))) (res_eq r));

// ALL2_1: chain form of ALL2 (¬(∀-merge)).
symbol ALL2_1 [n] [P : Tuple n → Tuple 1 → Prop]
  (r : Res (¬ (`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v))))
  : Res (¬ (`!! w : Tuple n, `!! y : Tuple 1, P w y))
  ≔ mk_1 (res_tm r) (eq_trans (eq_sym (not_cong (!!_split_eq P))) (res_eq r));

// ALL3_1: chain form of ALL3 ((∀-merge) ⇒ R).
symbol ALL3_1 [n] [P : Tuple n → Tuple 1 → Prop] [R : Prop]
  (r : Res ((`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)) ⇒ R))
  : Res ((`!! w : Tuple n, `!! y : Tuple 1, P w y) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (eq_sym (imp_cong_l (!!_split_eq P))) (res_eq r));

// ALL4_1: chain form of ALL4 (∀-merge).
symbol ALL4_1 [n] [P : Tuple n → Tuple 1 → Prop]
  (r : Res (`!! v : Tuple (n ++ 1), P (take [n] [1] v) (drop [n] [1] v)))
  : Res (`!! w : Tuple n, `!! y : Tuple 1, P w y)
  ≔ mk_1 (res_tm r) (eq_trans (eq_sym (!!_split_eq P)) (res_eq r));

// ALL6: Schema 1 — passthrough through `¬P ≡ P ⇒ ⊥` (a genuine HOAS identity).
// ALL7' / ALL8' / ALL9': special cases (see spec §8.13).

symbol ALL6_1 [n] [P : Tuple n → Prop]
  (r : Res ((`!! v, P v) ⇒ ⊥))
  : Res (¬ (`!! v, P v))
  ≔ mk_1 (res_tm r) (res_eq r);

// ALL7_1 (ALL7'): branching quantifier — per-tuple Res chain ρ +
// continuation r. The continuation premise uses `♢`
// (post-normalisation form per spec).
symbol ALL7_1 [n] [P : Tuple n → Prop] [Q : Prop]
  (ρ : Π v : Tuple n, Res (P v))
  (r : Res ((`♢ v, res_tm (ρ v)) ⇒ Q))
  : Res ((`!! v, P v) ⇒ Q) ≔
begin
  assume n P Q ρ r;
  refine mk_1 (res_tm r) _;
  have h1 : π ((`!! v, P v) = (`♢ v, res_tm (ρ v)))
    { refine eq_trans (!!_cong (λ v, res_eq (ρ v)))
        (eq_sym (♢_eq_!! (λ v, res_tm (ρ v)))) };
  have h2 : π (((`!! v, P v) ⇒ Q) = ((`♢ v, res_tm (ρ v)) ⇒ Q))
    { rewrite h1; reflexivity };
  refine eq_trans h2 (res_eq r)
end;

// ALL8_1 (ALL8'): congruence under ∀-block.
symbol ALL8_1 [n] [P : Tuple n → Prop]
  (ρ : Π v : Tuple n, Res (P v)) : Res (`!! v, P v)
  ≔ mk_1 (`!! v, res_tm (ρ v))
           (!!_cong (λ v, res_eq (ρ v)));

// ALL9_1 (ALL9'): result-form ALL9 (♡-block removal), mapping to (∀x·P) ⇒ R.
symbol ALL9_1 [n] [T : Tuple n → Prop] [Q : Prop]
  (r : Res Q) : Res ((`♡ v, T v) ⇒ Q)
  ≔ mk_1 ((`!! v, T v) ⇒ res_tm r)
          (eq_trans (imp_cong_l (♡_eq_!! T)) (imp_cong_r (res_eq r)));
