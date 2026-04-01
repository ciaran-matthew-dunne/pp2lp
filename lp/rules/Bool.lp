// Boolean (§A.15) — shallow encoding
// BTRUE, BFALSE : τ ι with bool_cases (guarded by ϵ BOOL).
require open pp2lp.B;

// ---- BOOL11/12: Context extension ----

// BOOL11: H, (v=TRUE), ¬(v=FALSE) ⊢ P → H ⊢ (v=TRUE) ⇒ P
opaque symbol BOOL11 [V : τ ι] [P : Prop]
  : (π (V = BTRUE) → π (¬ (V = BFALSE)) → π P)
  → π ((V = BTRUE) ⇒ P) ≔
begin
  assume V P h1 hvt;
  refine h1 hvt _;
  assume hvf;
  have h : π (BTRUE = BFALSE) { rewrite left hvt; refine hvf };
  refine bool_distinct h
end;

// BOOL12: H, (v=FALSE), ¬(v=TRUE) ⊢ P → H ⊢ (v=FALSE) ⇒ P
opaque symbol BOOL12 [V : τ ι] [P : Prop]
  : (π (V = BFALSE) → π (¬ (V = BTRUE)) → π P)
  → π ((V = BFALSE) ⇒ P) ≔
begin
  assume V P h1 hvf;
  refine h1 hvf _;
  assume hvt;
  have h : π (BTRUE = BFALSE) { rewrite left hvt; refine hvf };
  refine bool_distinct h
end;


// ---- BOOL21/22: Symmetry (provable) ----

// BOOL21: H ⊢ (v=TRUE) ⇒ P → H ⊢ (TRUE=v) ⇒ P
opaque symbol BOOL21 [V : τ ι] [P : Prop]
  : π ((V = BTRUE) ⇒ P)
  → π ((BTRUE = V) ⇒ P) ≔
begin
  assume V P h1 h2;
  refine h1 (eq_sym h2)
end;

// BOOL22: H ⊢ (v=FALSE) ⇒ P → H ⊢ (FALSE=v) ⇒ P
opaque symbol BOOL22 [V : τ ι] [P : Prop]
  : π ((V = BFALSE) ⇒ P)
  → π ((BFALSE = V) ⇒ P) ≔
begin
  assume V P h1 h2;
  refine h1 (eq_sym h2)
end;

// ---- BOOL31/32: Negation (provable with ϵ BOOL) ----

// BOOL31: H ⊢ (v=FALSE) ⇒ P → H ⊢ ¬(v=TRUE) ⇒ P
opaque symbol BOOL31 [V : τ ι] [P : Prop]
  : π ((V = BFALSE) ⇒ P)
  → π (¬ (V = BTRUE) ⇒ P) ≔
begin
admitted;

// BOOL32: H ⊢ (v=TRUE) ⇒ P → H ⊢ ¬(v=FALSE) ⇒ P
opaque symbol BOOL32 [V : τ ι] [P : Prop]
 : π ((V = BTRUE) ⇒ P)
  → π (¬ (V = BFALSE) ⇒ P) ≔
begin
admitted;

// ---- BOOL41/42: Negation + symmetry (provable with ϵ BOOL) ----

// BOOL41: H ⊢ (v=FALSE) ⇒ P → H ⊢ ¬(TRUE=v) ⇒ P
opaque symbol BOOL41 [v : τ ι] [P : Prop]
  : π ((v = BFALSE) ⇒ P)
  → π (¬ (BTRUE = v) ⇒ P) ≔
begin
  admitted;

// BOOL42: H ⊢ (v=TRUE) ⇒ P → H ⊢ ¬(FALSE=v) ⇒ P
opaque symbol BOOL42 [v : τ ι] [P : Prop]
  : π ((v = BTRUE) ⇒ P)
  → π (¬ (BFALSE = v) ⇒ P) ≔
begin
admitted;
// ---- BOOL51/52: Absurd boolean equality (leaf rules, arity 0) ----
// BOOL51: H ⊢ (TRUE = FALSE) ⇒ P
opaque symbol BOOL51 [P : Prop]
  : π ((BTRUE = BFALSE) ⇒ P) ≔
begin
  assume P h;
  refine ⊥ₑ (bool_distinct h)
end;

// BOOL52: H ⊢ (FALSE = TRUE) ⇒ P
opaque symbol BOOL52 [P : Prop]
  : π ((BFALSE = BTRUE) ⇒ P) ≔
begin
  assume P h;
  refine ⊥ₑ (bool_distinct (eq_sym h))
end;
