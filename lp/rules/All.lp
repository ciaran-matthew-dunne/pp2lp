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

require open pp2lp.B pp2lp.Quant;

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
//   premise 2: ((`!! v, res_tm (ρ v)) ⇒ Q) (continuation)
//   conclusion: (`!! v, P v) ⇒ Q
//
// The Res chain provides the equality proof internally via `res_eq`;
// the emitter constructs ρ as a chain of Res-yielding `_1` rules.

opaque symbol ALL7 [n] [P : Tuple n → Prop] [Q : Prop]
  (ρ : Π v : Tuple n, Res (P v))
  : π ((`!! v, res_tm (ρ v)) ⇒ Q) → π ((`!! v, P v) ⇒ Q) ≔
begin
  assume n P Q ρ h_after h_P;
  refine h_after (pi_to_!! (λ v, res_tm (ρ v))
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
// ♡ aliases ∀, so ♡-block = !!-block at the term level.

opaque symbol ALL9 [n] [T : Tuple n → Prop] [Q : Prop]
  : (π (`!! v, T v) → π Q)
  → π ((`!! v, T v) ⇒ Q) ≔
begin assume n T Q h; refine h end;
