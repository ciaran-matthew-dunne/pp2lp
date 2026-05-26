// Tuple-based n-ary quantifier machinery — foundations.
//
// `!!` and `??` are n-ary universal/existential quantifiers
// indexed by a Tuple n. The substantive rules (ALL4, ALL5, ALL7,
// XST5, XST7, XST8, …) live in lp/rules/All.lp and lp/rules/Xst.lp;
// this file only exposes the kernel needed to state and use them.
//
//   Tuple n        : an n-tuple of τ ι values
//   prj k v        : k-th projection (counts from the right;
//                    prj 0 v is the most recently appended element,
//                    which corresponds to the *outermost* `!!` binder)
//   `!! v : Tuple n, P v
//                  : `∀ x_1 ... ∀ x_n, P (unit ⨾ x_1 ⨾ … ⨾ x_n)`
//                    declared `quantifier`, so the standard sugar
//                    works:  `!! v, body`  ≡  `!! (λ v, body)`
//   `?? v : Tuple n, P v
//                  : analogous, with ∃ at every layer.
//
// Bridges:
//   pi_to_!!  : (Π v, π (P v))         → π (`!! v, P v)   — intro
//   !!_to_pi  : π (`!! v, P v)         → Π v, π (P v)     — elim
//   pi_to_??_intro : Π v, π (P v) → π (`?? v, P v)        — intro
//   pi_to_??_elim  : (Π v, π (P v) → π R) → π (`?? v, P v) → π R
//                                                          — elim
require open pp2lp.B;

// ---- Tuple ------------------------------------------------------

inductive Tuple : ℕ → TYPE ≔
  | unit : Tuple 0
  | ⨾ [n] : Tuple n → τ ι → Tuple (+1 n);
notation ⨾ infix left 5;
//type ind_Tuple;
// k-th projection. prj 0 picks the rightmost (most recently
// appended) element.
symbol prj [n] (k : ℕ) (_ : Tuple n) : τ ι;
rule prj (+1 $n) ($t ⨾ _) ↪ prj $n $t
with prj 0       (_ ⨾ $x) ↪ $x;

// Canonical inhabitant of `Tuple n` — every slot filled with `inh`.
// Used when a rule needs a witness tuple but its predicate is
// independent of the tuple's contents.
symbol inh_tuple [n] : Tuple n;
rule inh_tuple [0] ↪ unit
with inh_tuple [+1 $n] ↪ inh_tuple [$n] ⨾ inh;

// ---- Tuple split: `++`, take, drop --------------------------------
// Custom natural-number addition that recurses on the LEFT, unlike
// Stdlib.Nat.+ which only reduces when the right arg is `+1 _`. This
// lets `Tuple ((+1 n) ++ m)` reduce to `Tuple (+1 (n ++ m))` so its
// inhabitants are recognisable as tuple constructors `(_ ⨾ _)`.
symbol ++ : ℕ → ℕ → ℕ; notation ++ infix 5;
rule 0 ++ $m ↪ $m
with +1 $n ++ $m ↪ +1 ($n ++ $m);

// `take [n] [m]` extracts the leftmost n elements of a (n+m)-tuple.
// `drop [n] [m]` extracts the rightmost m elements (what remains).
// Convention: in `(unit ⨾ x_1 ⨾ … ⨾ x_n ⨾ y_1 ⨾ … ⨾ y_m)`, take returns
// `(unit ⨾ x_1 ⨾ … ⨾ x_n)` and drop returns `(unit ⨾ y_1 ⨾ … ⨾ y_m)`.
// Concretely, drop strips the rightmost m elements first; take returns
// what's left after recursively peeling.
//
// Compared to inh-based subtraction: avoids needing `(n + m) - n = m`
// to be definitional (which it isn't for abstract n, m). Indices are
// kept explicit so call sites can name them and the rules fire.
symbol take [n m] (v : Tuple (n ++ m)) : Tuple n;
symbol drop [n m] (v : Tuple (n ++ m)) : Tuple m;
rule drop [0]      [_]  $v        ↪ $v
with drop [+1 $n] [$m] ($v ⨾ _)   ↪ drop [$n] [$m] $v
with take [0]      [_]  _         ↪ unit
with take [+1 $n] [$m] ($v ⨾ $x)  ↪ take [$n] [$m] $v ⨾ $x;

// ---- `!!` n-ary universal --------------------------------------

// Kept *rigid* (no reduction rules). If `!!` reduced eagerly to
// nested ∀, the surface form would vanish from goals before any
// tactic could see it — and implicit-arg inference of `n` and `P`
// at call sites would need to invert the reduction (higher-order
// unification across rewriting), which Lambdapi can't.
constant symbol !! [n] : (Tuple n → Prop) → Prop;
notation !! quantifier;

constant symbol pi_to_!! [n] (P : Tuple n → Prop)
  : (Π v : Tuple n, π (P v)) → π (`!! v, P v);

constant symbol !!_to_pi [n] (P : Tuple n → Prop)
  : π (`!! v, P v) → Π v : Tuple n, π (P v);

// ---- `??` n-ary existential ------------------------------------
//
// Kept *rigid* like `!!`. Earlier we let `??` reduce to nested ∃,
// but that broke implicit-P inference at sites like XST7_1's body
// (HO-unification can't invert the reduction). Bridges are
// axiomatised below.

constant symbol ?? [n] : (Tuple n → Prop) → Prop;
notation ?? quantifier;

constant symbol pi_to_??_intro [n] (P : Tuple n → Prop)
  : Π v : Tuple n, π (P v) → π (`?? v, P v);

constant symbol pi_to_??_elim [n] (P : Tuple n → Prop) [R : Prop]
  : (Π v : Tuple n, π (P v) → π R) → π (`?? v, P v) → π R;

// ---- Common derived lemmas -------------------------------------

// Pointwise equality lifts to `!!` equality.
opaque symbol !!_cong [n] [P R : Tuple n → Prop]
  : (Π v : Tuple n, π (P v = R v))
  → π ((`!! v, P v) = (`!! v, R v)) ≔
begin
  assume n P R h;
  refine propExt _ _ _ _
  { assume hP; refine pi_to_!! R (λ v, =⇒ (h v) (!!_to_pi P hP v)) }
  { assume hR; refine pi_to_!! P (λ v, =⇒ (eq_sym (h v)) (!!_to_pi R hR v)) }
end;

// Pointwise equality lifts to `??` equality.
opaque symbol ??_cong [n] [P R : Tuple n → Prop]
  : (Π v : Tuple n, π (P v = R v))
  → π ((`?? v, P v) = (`?? v, R v)) ≔
begin
  assume n P R h;
  refine propExt _ _ _ _
  { assume hP; refine pi_to_??_elim P
      (λ v hPv, pi_to_??_intro R v (=⇒ (h v) hPv)) hP }
  { assume hR; refine pi_to_??_elim R
      (λ v hRv, pi_to_??_intro P v (=⇒ (eq_sym (h v)) hRv)) hR }
end;

// `!!_const`: drop a constant `!!`-binder. Tuple-n analogue of
// Stdlib.PropExt's `∀_const`. Both directions go through `inh_tuple`.
opaque symbol !!_const [n] (P : Prop)
  : π ((`!! _ : Tuple n, P) = P) ≔
begin
  assume n P;
  refine propExt _ _ _ _
  { assume h; refine !!_to_pi (λ _ : Tuple n, P) h (inh_tuple [n]) }
  { assume h; refine pi_to_!! (λ _ : Tuple n, P) (λ _, h) }
end;

// ---- ♢ / ♡ : PP normalisation quantifiers ----------------------
//
// Spec uses `♢` (= ASCII `forall`) for goal-side n-ary universals and
// `♡` (= ASCII `forall2`) for hypothesis-side ones. Semantically both
// are nested ∀ — they only carry a proof-search role.
//
// Kept *rigid* (constant, no rewrite rules) for the same reason `!!`
// is rigid. The reduction to `!!` is axiomatised: `pi_to_♢` /
// `♢_to_pi` are the per-tuple bridges; `♢_eq_!!` follows from
// `propExt`. NRM rules state their types in spec notation; bodies use
// the dedicated bridges or transport via `♢_eq_!!` where helpers are
// `!!`-typed.

constant symbol ♢ [n] : (Tuple n → Prop) → Prop;
notation ♢ quantifier;

constant symbol pi_to_♢ [n] (P : Tuple n → Prop)
  : (Π v : Tuple n, π (P v)) → π (`♢ v, P v);

constant symbol ♢_to_pi [n] (P : Tuple n → Prop)
  : π (`♢ v, P v) → Π v : Tuple n, π (P v);

constant symbol ♡ [n] : (Tuple n → Prop) → Prop;
notation ♡ quantifier;

constant symbol pi_to_♡ [n] (P : Tuple n → Prop)
  : (Π v : Tuple n, π (P v)) → π (`♡ v, P v);

constant symbol ♡_to_pi [n] (P : Tuple n → Prop)
  : π (`♡ v, P v) → Π v : Tuple n, π (P v);

// Both ♢ and ♡ are propositionally equal to `!!` — derived from the
// bridges via `propExt`.
opaque symbol ♢_eq_!! [n] (P : Tuple n → Prop)
  : π ((`♢ v, P v) = (`!! v, P v)) ≔
begin
  assume n P;
  refine propExt _ _ _ _
  { assume h; refine pi_to_!! P (♢_to_pi P h) }
  { assume h; refine pi_to_♢ P (!!_to_pi P h) }
end;

opaque symbol ♡_eq_!! [n] (P : Tuple n → Prop)
  : π ((`♡ v, P v) = (`!! v, P v)) ≔
begin
  assume n P;
  refine propExt _ _ _ _
  { assume h; refine pi_to_!! P (♡_to_pi P h) }
  { assume h; refine pi_to_♡ P (!!_to_pi P h) }
end;

// ---- Res: Σ-type for normalisation chains ----------------------
// `Res t = (t' : τ a) × π (t = t')` packages a normalised term with
// a proof of equality to the original. Lives here (not in Res.lp)
// because the result-based ALL7/XST8 in All.lp/Xst.lp need it.
injective symbol Res [a : Set] : τ a → TYPE;
symbol mk_1 [a t] (t' : τ a) : π (t = t') → Res t;
symbol res_tm [a t] : Res [a] t → τ a;
symbol res_eq [a t] (r : Res [a] t) : π (t = res_tm r);
rule res_tm (mk_1 $t' _) ↪ $t';
rule res_eq (mk_1 _ $prf) ↪ $prf;
