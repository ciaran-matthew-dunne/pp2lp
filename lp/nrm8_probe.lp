// Probe: replicate the take/drop-based NRM8 from nrm_test.lp and
// check whether Lambdapi can apply it to a goal shaped like og/19.
//
// The realistic body uses raw τ ι projections of the bound tuples
// (because PP-emitted bodies extract individual elements via prj):
//   (prj 0 x ↦ prj 0 y) ϵ p ⇒ (prj 0 x ↦ eapp p (prj 0 x)) ϵ p
// So Q = λ x y, body — a clean HO pattern (x and y appear directly
// inside Q's body), which Lambdapi's pattern unifier can handle.

require open pp2lp.B pp2lp.Quant;

// Custom `++` that recurses on the LEFT argument — unlike Stdlib.Nat.+
// which only reduces when the right arg is +1. This lets us pattern-match
// on `(+1 n) ++ m ≡ +1 (n ++ m)` so a Tuple ((+1 n) ++ m) value is
// recognisable as a Tuple constructor `(v ⨾ x)`.
symbol ++ : ℕ → ℕ → ℕ; notation ++ infix 5;
rule 0 ++ $m ↪ $m
with +1 $n ++ $m ↪ +1 ($n ++ $m);

// Split a `Tuple (n ++ m)` into its prefix (Tuple n) and suffix (Tuple m).
symbol take [n m] (v : Tuple (n ++ m)) : Tuple n;
rule take [0] [_] _ ↪ unit
with take [+1 $n] [$m] ($v ⨾ $x) ↪ take [$n] [$m] $v ⨾ $x;

symbol drop [n m] (v : Tuple (n ++ m)) : Tuple m;
rule drop [0] [_] $v ↪ $v
with drop [+1 $n] [$m] ($v ⨾ _) ↪ drop [$n] [$m] $v;

// Polymorphic NRM8 — should typecheck because the Tuple types in the
// premise reduce: `take` returns Tuple n, `drop` returns Tuple m by
// definition (no subtraction).
constant symbol NRM8 [n m] [Q : Tuple n → Tuple m → Prop] [S : Prop]
  : π ((`!! v : Tuple (n ++ m),
         Q (take [n] [m] v) (drop [n] [m] v)) ⇒ S)
  → π ((`♢ x : Tuple n, `!! y : Tuple m, Q x y) ⇒ S);

// og/19's pre-NRM8 shape (with the body as the raw τ ι projections).
//
// Body abstracted into a τ ι → τ ι → Prop function so we can compare
// shapes cleanly without operator-parsing complications.
symbol body : τ ι → τ ι → Prop;

opaque symbol probe_og19 (S : Prop)
  : π ((`!! v : Tuple (1 ++ 1),
         body (prj 0 (take [1] [1] v)) (prj 0 (drop [1] [1] v))) ⇒ S)
  → π ((`♢ x : Tuple 1, `!! y : Tuple 1,
         body (prj 0 x) (prj 0 y)) ⇒ S) ≔
begin
  assume S h;
  refine NRM8 _;
  refine h
end;

// og/21-style: NRM8(2) — outer ♢ over Tuple 2, inner !! over Tuple 1.
//   forall(x$6, x$5).!(x$7).(x$6,x$5,x$7: q => x$6,x$5,q(x$6,x$5): q)
//                 ⇒ p ∨ ¬ p
// → forall(x$6, x$5, x$7).(x$6,x$5,x$7: q => x$6,x$5,q(x$6,x$5): q) ⇒ ...
symbol body3 : τ ι → τ ι → τ ι → Prop;

opaque symbol probe_og21 (S : Prop)
  : π ((`!! v : Tuple (2 ++ 1),
         body3 (prj _1 (take [2] [1] v))
               (prj 0 (take [2] [1] v))
               (prj 0 (drop [2] [1] v))) ⇒ S)
  → π ((`♢ x : Tuple 2, `!! y : Tuple 1,
         body3 (prj _1 x) (prj 0 x) (prj 0 y)) ⇒ S) ≔
begin
  assume S h;
  refine NRM8 _;
  refine h
end;

// What if the emitter wrote the post-NRM8 body using straight projections
// of `v` (current convention: x_i → prj _i v) instead of through take/drop?
// Then NRM8's premise would not match Q (take v) (drop v) shape.
// probe_og21_naive — DEMONSTRATES THAT THE EMITTER CANNOT use plain
// `prj _i v` for the post-NRM8 body; it must thread projections through
// `take`/`drop`. After `refine NRM8 _;` Lambdapi leaves the goal:
//   body3 (prj _2 v) (prj _1 v) (prj 0 v)
//     ≡ body3 (prj _1 (take v)) (prj 0 (take v)) (prj 0 (drop v))
// — semantically equal but not definitionally, since `take`/`drop` only
// reduce on tuple-constructor structure, and `v` is bound abstractly.
//
// (commented out so this file checks)

// Convention check on concrete tuples — note semantics:
//   `take [n] [m]` returns the RIGHTMOST n (i.e. the most-recently
//   appended n elements);
//   `drop [n] [m]` returns the LEFTMOST m (i.e. what remains after
//   stripping n from the right).
// So in NRM8 with conclusion `(`♢ x : Tuple n, `!! y : Tuple m, Q x y)`,
// where the inner-most bound `y` lives at the right of the joined
// tuple, `take v` actually corresponds to *y* and `drop v` to *x*.
// The user's NRM8 statement passes them as `Q (take v) (drop v)` —
// this binds Q's first arg (declared `Tuple n` = x) to the rightmost-n
// elements (y's positions). To keep the spec convention (Q's first
// arg = x), the call order should be `Q (drop v) (take v)`.
opaque symbol concrete_take (a b : τ ι)
  : π (prj 0 (take [1] [1] (unit ⨾ a ⨾ b)) = b) ≔
begin reflexivity end;

opaque symbol concrete_drop (a b : τ ι)
  : π (prj 0 (drop [1] [1] (unit ⨾ a ⨾ b)) = a) ≔
begin reflexivity end;
