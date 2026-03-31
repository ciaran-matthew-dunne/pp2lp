// Boolean (§A.15) — shallow encoding
// BTRUE, BFALSE : τ ι with bool_cases (guarded by ϵ BOOL).
require open pp2lp.B;

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
  : π (V ϵ BOOL)
  → π ((V = BFALSE) ⇒ P)
  → π (¬ (V = BTRUE) ⇒ P) ≔
begin
  assume V P hb h1 h2;
  refine ∨ₑ (bool_cases V hb) _ _ {
    assume ht; refine ⊥ₑ (h2 ht)
  } {
    assume hf; refine h1 hf
  }
end;

// BOOL32: H ⊢ (v=TRUE) ⇒ P → H ⊢ ¬(v=FALSE) ⇒ P
opaque symbol BOOL32 [V : τ ι] [P : Prop]
  : π (V ϵ BOOL)
  → π ((V = BTRUE) ⇒ P)
  → π (¬ (V = BFALSE) ⇒ P) ≔
begin
  assume V P hb h1 h2;
  refine ∨ₑ (bool_cases V hb) _ _ {
    assume ht; refine h1 ht
  } {
    assume hf; refine ⊥ₑ (h2 hf)
  }
end;

// ---- BOOL41/42: Negation + symmetry (provable with ϵ BOOL) ----

// BOOL41: H ⊢ (v=FALSE) ⇒ P → H ⊢ ¬(TRUE=v) ⇒ P
opaque symbol BOOL41 [V : τ ι] [P : Prop]
  : π (V ϵ BOOL)
  → π ((BFALSE = V) ⇒ P)
  → π (¬ (V = BTRUE) ⇒ P) ≔
begin
  assume V P hb h1 h2;
  refine ∨ₑ (bool_cases V hb) _ _ {
    assume ht; refine ⊥ₑ (h2 ht)
  } {
    assume hf; refine h1 (eq_sym hf)
  }
end;

// BOOL42: H ⊢ (v=TRUE) ⇒ P → H ⊢ ¬(FALSE=v) ⇒ P
opaque symbol BOOL42 [V : τ ι] [P : Prop]
  : π (V ϵ BOOL)
  → π ((BTRUE = V) ⇒ P)
  → π (¬ (V = BFALSE) ⇒ P) ≔
begin
  assume V P hb h1 h2;
  refine ∨ₑ (bool_cases V hb) _ _ {
    assume ht; refine h1 (eq_sym ht)
  } {
    assume hf; refine ⊥ₑ (h2 hf)
  }
end;

// ---- BOOL51/52: Boolean case analysis helpers ----
// Spec BOOL51: H ⊢ (TRUE=FALSE) ⇒ P
// Spec BOOL52: H ⊢ ¬(FALSE=TRUE) ⇒ P
// Implementation: derive v=FALSE from ¬(v=TRUE) (and vice versa) given v ∈ BOOL.

// BOOL51: v ∈ BOOL; ¬(v=TRUE) → v=FALSE
opaque symbol BOOL51 [V : τ ι]
  : π (V ϵ BOOL)
  → π (¬ (V = BTRUE))
  → π (V = BFALSE) ≔
begin
  assume V hb h;
  refine ∨ₑ (bool_cases V hb) _ _ {
    assume ht; refine ⊥ₑ (h ht)
  } {
    assume hf; refine hf
  }
end;

// BOOL52: v ∈ BOOL; ¬(v=FALSE) → v=TRUE
opaque symbol BOOL52 [V : τ ι]
  : π (V ϵ BOOL)
  → π (¬ (V = BFALSE))
  → π (V = BTRUE) ≔
begin
  assume V hb h;
  refine ∨ₑ (bool_cases V hb) _ _ {
    assume ht; refine ht
  } {
    assume hf; refine ⊥ₑ (h hf)
  }
end;

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
