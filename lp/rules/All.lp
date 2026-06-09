// Universal quantification (§A.7) — tuple-based encoding.
//
// Compound bindings in PP traces map to `!! v : Tuple n, P v`. The
// per-arity scaffolding the previous version of this file carried
// (ALL5_2, ALL7_2, ALL7_3, ALL7_2i, ALL7_3i, …) is gone: the uniform
// tuple-indexed forms below subsume every arity.
//
// ALL1–4 are compound↔nested conversions. Per the spec convention,
// `x` is an n-tuple bundle and `y` is the singleton trailing var,
// so the rule peels one layer at a time:
//
//   compound : `!! v : Tuple (+1 n), P v
//   nested   : `!! w : Tuple n, `!! y : Tuple 1, P (w ⨾ prj 0 y)
//
// Tuple (+1 n) constructors are exactly `(w ⨾ a)`, so the harder
// direction (nested → compound) is provable by a rewrite rule that
// pattern-matches on the constructor.

require open pp2lp.B pp2lp.Quant pp2lp.rules.Res;

// Helper: nested → compound. Defined by rewrite rule on the
// tuple constructor `($w ⨾ $a)`. Used by ALL2, ALL3.
symbol nested_to_compound [n] (P : Tuple (+1 n) → Prop)
  (h : π (`!! w : Tuple n, `!! y : Tuple 1, P (w ⨾ prj 0 y)))
  : Π v : Tuple (+1 n), π (P v);
rule nested_to_compound [$n] $P $h ($w ⨾ $a) ↪
  !!_to_pi (λ y, $P ($w ⨾ prj 0 y))
           (!!_to_pi (λ w, `!! y : Tuple 1, $P (w ⨾ prj 0 y)) $h $w)
           (unit ⨾ $a);

// ALL1: H ⊢ ¬(∀(x,y)·P) ⇒ R → H ⊢ ¬(∀x·∀y·P) ⇒ R
opaque symbol ALL1 [n] [P : Tuple (+1 n) → Prop] [R : Prop]
  : π (¬ (`!! v : Tuple (+1 n), P v) ⇒ R)
  → π (¬ (`!! w : Tuple n, `!! y : Tuple 1, P (w ⨾ prj 0 y)) ⇒ R) ≔
begin
  assume n P R h hnnested;
  refine h _;
  assume hcompound;
  refine hnnested _;
  refine pi_to_!! _ _; assume w;
  refine pi_to_!! _ _; assume y;
  refine !!_to_pi P hcompound (w ⨾ prj 0 y)
end;

// ALL2: H ⊢ ¬(∀(x,y)·P) → H ⊢ ¬(∀x·∀y·P)
opaque symbol ALL2 [n] [P : Tuple (+1 n) → Prop]
  : π (¬ (`!! v : Tuple (+1 n), P v))
  → π (¬ (`!! w : Tuple n, `!! y : Tuple 1, P (w ⨾ prj 0 y))) ≔
begin
  assume n P h hnested;
  refine h (pi_to_!! P (nested_to_compound P hnested))
end;

// ALL3: H ⊢ (∀(x,y)·P) ⇒ R → H ⊢ (∀x·∀y·P) ⇒ R
opaque symbol ALL3 [n] [P : Tuple (+1 n) → Prop] [R : Prop]
  : π ((`!! v : Tuple (+1 n), P v) ⇒ R)
  → π ((`!! w : Tuple n, `!! y : Tuple 1, P (w ⨾ prj 0 y)) ⇒ R) ≔
begin
  assume n P R h hnested;
  refine h (pi_to_!! P (nested_to_compound P hnested))
end;

// ALL3R: ALL3 with the *outer* binder appended last.  A branching
// continuation's goal `(!! v, res_tm (ρ v)) ⇒ R` is structurally nested
// when the chain result is itself a universal; merging it with ALL3 would
// put the inner binder at `prj 0`, the opposite of the renderer's
// slot order (first PP binder ↦ prj 0).  ALL3R appends the outer
// element instead (`y ⨾ prj 0 w`), so its compound premise matches the
// renderer's convention and downstream hyp searches stay consistent.
symbol nested_to_compoundR [n] (P : Tuple (+1 n) → Prop)
  (h : π (`!! w : Tuple 1, `!! y : Tuple n, P (y ⨾ prj 0 w)))
  : Π v : Tuple (+1 n), π (P v);
rule nested_to_compoundR [$n] $P $h ($y ⨾ $a) ↪
  !!_to_pi (λ y, $P (y ⨾ $a))
           (!!_to_pi (λ w, `!! y : Tuple $n, $P (y ⨾ prj 0 w)) $h (unit ⨾ $a))
           $y;

opaque symbol ALL3R [n] [P : Tuple (+1 n) → Prop] [R : Prop]
  : π ((`!! v : Tuple (+1 n), P v) ⇒ R)
  → π ((`!! w : Tuple 1, `!! y : Tuple n, P (y ⨾ prj 0 w)) ⇒ R) ≔
begin
  assume n P R h hnested;
  refine h (pi_to_!! P (nested_to_compoundR P hnested))
end;

// ALL4: H ⊢ ∀(x,y)·P → H ⊢ ∀x·∀y·P
opaque symbol ALL4 [n] [P : Tuple (+1 n) → Prop]
  : π (`!! v : Tuple (+1 n), P v)
  → π (`!! w : Tuple n, `!! y : Tuple 1, P (w ⨾ prj 0 y)) ≔
begin
  assume n P h;
  refine pi_to_!! _ _; assume w;
  refine pi_to_!! _ _; assume y;
  refine !!_to_pi P h (w ⨾ prj 0 y)
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
// ALL1–ALL6: Schema 1 passthrough. ALL1–4 are compound↔nested
// conversions whose LP encoding is HOAS-identity at the value level;
// res_tm propagates via `trust` for the equality bridge between the
// compound and nested forms.
// ALL5: Schema 1 — passthrough through the `¬∀ ⇒ R = ∀ ¬ ⇒ R` bridge.
// ALL6: Schema 1 — passthrough through `¬P ≡ P ⇒ ⊥`.
// ALL7' / ALL8' / ALL9': special cases (see spec §8.13).

symbol ALL1_1 [n] [P : Tuple (+1 n) → Prop] [R : Prop]
  (r : Res (¬ (`!! v : Tuple (+1 n), P v) ⇒ R))
  : Res (¬ (`!! w : Tuple n, `!! y : Tuple 1, P (w ⨾ prj 0 y)) ⇒ R)
  ≔ mk_1 (res_tm r) trust;

symbol ALL2_1 [n] [P : Tuple (+1 n) → Prop]
  (r : Res (¬ (`!! v : Tuple (+1 n), P v)))
  : Res (¬ (`!! w : Tuple n, `!! y : Tuple 1, P (w ⨾ prj 0 y)))
  ≔ mk_1 (res_tm r) trust;

symbol ALL3_1 [n] [P : Tuple (+1 n) → Prop] [R : Prop]
  (r : Res ((`!! v : Tuple (+1 n), P v) ⇒ R))
  : Res ((`!! w : Tuple n, `!! y : Tuple 1, P (w ⨾ prj 0 y)) ⇒ R)
  ≔ mk_1 (res_tm r) trust;

// Chain form of ALL3R (outer binder appended last; see ALL3R above).
symbol ALL3R_1 [n] [P : Tuple (+1 n) → Prop] [R : Prop]
  (r : Res ((`!! v : Tuple (+1 n), P v) ⇒ R))
  : Res ((`!! w : Tuple 1, `!! y : Tuple n, P (y ⨾ prj 0 w)) ⇒ R)
  ≔ mk_1 (res_tm r) trust;

symbol ALL4_1 [n] [P : Tuple (+1 n) → Prop]
  (r : Res (`!! v : Tuple (+1 n), P v))
  : Res (`!! w : Tuple n, `!! y : Tuple 1, P (w ⨾ prj 0 y))
  ≔ mk_1 (res_tm r) trust;

symbol ALL5_1 [n] [P : Tuple n → Prop] [R : Prop]
  (r : Res (`!! v, ¬ (P v) ⇒ R))
  : Res (¬ (`!! v, P v) ⇒ R)
  ≔ mk_1 (res_tm r) trust;

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
