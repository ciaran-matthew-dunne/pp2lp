// Boolean (§A.15) — shallow encoding
// BTRUE, BFALSE : τ ι with bool_cases (guarded by ϵ BOOL).
require open pp2lp.B pp2lp.Quant pp2lp.rules.Res;

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

// ---- BOOL31/32: Negation (proved via bool_cases + ϵ BOOL) ----

// BOOL31: H ⊢ (v=FALSE) ⇒ P → H ⊢ ¬(v=TRUE) ⇒ P
opaque symbol BOOL31 [V : τ ι] [P : Prop]
  (hb : π (V ϵ BOOL))
  : π ((V = BFALSE) ⇒ P)
  → π (¬ (V = BTRUE) ⇒ P) ≔
begin
  assume V P hb h1 hnt;
  have hcases : π (V = BTRUE ∨ V = BFALSE) { refine bool_cases V hb };
  refine ∨ₑ hcases _ _
  { assume hvt; refine ⊥ₑ (hnt hvt) }
  { assume hvf; refine h1 hvf }
end;

// BOOL32: H ⊢ (v=TRUE) ⇒ P → H ⊢ ¬(v=FALSE) ⇒ P
opaque symbol BOOL32 [V : τ ι] [P : Prop]
  (hb : π (V ϵ BOOL))
  : π ((V = BTRUE) ⇒ P)
  → π (¬ (V = BFALSE) ⇒ P) ≔
begin
  assume V P hb h1 hnt;
  have hcases : π (V = BTRUE ∨ V = BFALSE) { refine bool_cases V hb };
  refine ∨ₑ hcases _ _
  { assume hvt; refine h1 hvt }
  { assume hvf; refine ⊥ₑ (hnt hvf) }
end;

// ---- BOOL41/42: Negation + symmetry (proved via bool_cases + ϵ BOOL) ----

// BOOL41: H ⊢ (v=FALSE) ⇒ P → H ⊢ ¬(TRUE=v) ⇒ P
opaque symbol BOOL41 [v : τ ι] [P : Prop]
  (hb : π (v ϵ BOOL))
  : π ((v = BFALSE) ⇒ P)
  → π (¬ (BTRUE = v) ⇒ P) ≔
begin
  assume v P hb h1 hnt;
  have hcases : π (v = BTRUE ∨ v = BFALSE) { refine bool_cases v hb };
  refine ∨ₑ hcases _ _
  { assume hvt; refine ⊥ₑ (hnt (eq_sym hvt)) }
  { assume hvf; refine h1 hvf }
end;

// BOOL42: H ⊢ (v=TRUE) ⇒ P → H ⊢ ¬(FALSE=v) ⇒ P
opaque symbol BOOL42 [v : τ ι] [P : Prop]
  (hb : π (v ϵ BOOL))
  : π ((v = BTRUE) ⇒ P)
  → π (¬ (BFALSE = v) ⇒ P) ≔
begin
  assume v P hb h1 hnt;
  have hcases : π (v = BTRUE ∨ v = BFALSE) { refine bool_cases v hb };
  refine ∨ₑ hcases _ _
  { assume hvt; refine h1 hvt }
  { assume hvf; refine ⊥ₑ (hnt (eq_sym hvf)) }
end;
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

// ---- `_1` (Result-form) variants — §8.13 ----
//
// BOOL11/12: Schema 1 with antecedent introduction (HOAS).
// BOOL21/22: Schema 1 passthrough through eq commutativity.
// BOOL31/32/41/42: Schema 1 with the `V ϵ BOOL` side-condition.
// BOOL51/52: Schema 0 — `bool_distinct` makes the antecedent ⊥.

symbol BOOL11_1 [V : τ ι] [P : Prop]
  (r : Res P) : Res ((V = BTRUE) ⇒ P)
  ≔ mk_1 (res_tm r) trust;

symbol BOOL12_1 [V : τ ι] [P : Prop]
  (r : Res P) : Res ((V = BFALSE) ⇒ P)
  ≔ mk_1 (res_tm r) trust;

symbol BOOL21_1 [V : τ ι] [P : Prop]
  (r : Res ((V = BTRUE) ⇒ P)) : Res ((BTRUE = V) ⇒ P)
  ≔ mk_1 (res_tm r) (eq_trans (imp_cong_l (eq_comm_prop BTRUE V)) (res_eq r));

symbol BOOL22_1 [V : τ ι] [P : Prop]
  (r : Res ((V = BFALSE) ⇒ P)) : Res ((BFALSE = V) ⇒ P)
  ≔ mk_1 (res_tm r) (eq_trans (imp_cong_l (eq_comm_prop BFALSE V)) (res_eq r));

symbol BOOL31_1 [V : τ ι] [P : Prop]
  (hb : π (V ϵ BOOL)) (r : Res ((V = BFALSE) ⇒ P))
  : Res (¬ (V = BTRUE) ⇒ P)
  ≔ mk_1 (res_tm r) trust;

symbol BOOL32_1 [V : τ ι] [P : Prop]
  (hb : π (V ϵ BOOL)) (r : Res ((V = BTRUE) ⇒ P))
  : Res (¬ (V = BFALSE) ⇒ P)
  ≔ mk_1 (res_tm r) trust;

symbol BOOL41_1 [V : τ ι] [P : Prop]
  (hb : π (V ϵ BOOL)) (r : Res ((V = BFALSE) ⇒ P))
  : Res (¬ (BTRUE = V) ⇒ P)
  ≔ mk_1 (res_tm r) trust;

symbol BOOL42_1 [V : τ ι] [P : Prop]
  (hb : π (V ϵ BOOL)) (r : Res ((V = BTRUE) ⇒ P))
  : Res (¬ (BFALSE = V) ⇒ P)
  ≔ mk_1 (res_tm r) trust;

// BTRUE = BFALSE is absurd (bool_distinct), so the implication is vacuously ⊤.
symbol BOOL51_1 [P : Prop] : Res ((BTRUE = BFALSE) ⇒ P)
  ≔ mk_0 (prop_eq_top BOOL51);
symbol BOOL52_1 [P : Prop] : Res ((BFALSE = BTRUE) ⇒ P)
  ≔ mk_0 (prop_eq_top BOOL52);
