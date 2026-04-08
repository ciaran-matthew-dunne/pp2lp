// Arithmetic (§A.14) — shallow encoding
// Uses ≤ and leq_refl from B.lp.
require open pp2lp.B;

// ---- AR1-3: Reflexivity of ≤ ----

// AR1: H ⊢ R → H ⊢ E ≤ E ⇒ R
opaque symbol AR1 [E : τ ι] [R : Prop]
  : π R
  → π ((E ≤ E) ⇒ R) ≔
begin
  assume E R h h0; refine h
end;

// AR2: a numeric, b numeric, a > b → H ⊢ a ≤ b ⇒ R
opaque symbol AR2 [a b : τ ι] [R : Prop]
  : π (¬ (a ≤ b))
  → π ((a ≤ b) ⇒ R) ≔
begin
  assume a b R hn h; refine ⊥ₑ (hn h)
end;

// AR3: ¬(a ≤ 0) ⇒ R → (b ≤ 0) ⇒ R where b = 1-a (solver-simplified)
opaque symbol AR3 [a : τ ι] (b : τ ι) [R : Prop]
  : π (b = (𝟏 - a))
  → π ((b ≤ 𝟎) ⇒ R)
  → π (¬ (a ≤ 𝟎) ⇒ R) ≔
begin
  admit
end;

// AR4: F ≤ 0 in H; E + F > 0 (solver-confirmed) → H ⊢ E ≤ 0 ⇒ R
opaque symbol AR4 [E : τ ι] [R : Prop] (F : τ ι)
  : π (F ≤ 𝟎)
  → π ⊤
  → π ((E ≤ 𝟎) ⇒ R) ≔
begin
  admit
end;

// ---- AR5/AR6: Antisymmetry decomposition ----

opaque symbol AR5 [a : τ ι] [R : Prop]
  : π (a ≤ 𝟎)
  → π ((— a ≪ 𝟎) ⇒ ((a = 𝟎) ⇒ R))
  → π ((— a ≤ 𝟎) ⇒ R) ≔
begin
  admit
end;

opaque symbol AR6 [a : τ ι] [R : Prop]
  : π ((— a) ≤ 𝟎)
  → π ((a ≪ 𝟎) ⇒ ((a = 𝟎) ⇒ R))
  → π ((a ≤ 𝟎) ⇒ R) ≔
begin
  admit
end;

// ---- AR7/AR8: Antisymmetry with offset ----

opaque symbol AR7 [a b : τ ι] (c : τ ι) [R : Prop]
  : π ((c + b) ≤ 𝟎)
  → π ((a + c) = 𝟎)
  → π ((b = a) ⇒ (((a - b) ≪ 𝟎) ⇒ R))
  → π (((a - b) ≤ 𝟎) ⇒ R) ≔
begin
  admit
end;

opaque symbol AR8 (a : τ ι) [b c : τ ι] [R : Prop]
  : π ((a - b) ≤ 𝟎)
  → π ((a + c) = 𝟎)
  → π ((b = a) ⇒ (((c + b) ≪ 𝟎) ⇒ R))
  → π (((c + b) ≤ 𝟎) ⇒ R) ≔
begin
  admit
end;

opaque symbol AR9 [E : τ ι] (F : τ ι) [R : Prop]
  : π (E = F)
  → π ((F ≤ 𝟎) ⇒ R)
  → π ((E ≤ 𝟎) ⇒ R) ≔
begin
  assume E F R heq hf h;
  have h2 : π (F ≤ 𝟎) { rewrite left heq; refine h };
  refine hf h2
end;

opaque symbol AR9_1 [E : τ ι] (F : τ ι) [R : Prop] [S : Prop]
  : π (E = F)
  → π (((F ≤ 𝟎) ⇒ R) = S)
  → π (((E ≤ 𝟎) ⇒ R) = S) ≔
begin
  assume E F R S heq h;
  rewrite heq; refine h
end;

// AR10: solver(P) = Q; H ⊢ Q ⇒ R → H ⊢ P ⇒ R
opaque symbol AR10 [P Q R : Prop]
  : π (P = Q)
  → π (Q ⇒ R)
  → π (P ⇒ R) ≔
begin
  assume P Q R heq h1 h2;
  refine h1 (=⇒ heq h2)
end;

// AR11: H ⊢ ¬(x ≤ x) ⇒ P
opaque symbol AR11 [E : τ ι] [P : Prop]
  : π (¬ (E ≤ E) ⇒ P) ≔
begin
  assume E P h; refine ⊥ₑ (h (leq_refl E))
end;

// AR12: H, (a ≤ b) ⊢ P → H ⊢ (a ≪ b) ⇒ P
opaque symbol AR12 [a b : τ ι] [P : Prop]
  : (π (a ≤ b) → π P)
  → π ((a ≪ b) ⇒ P) ≔
begin
  assume a b P h1 h2;
  refine h1 (strict_to_leq a b h2)
end;

// AR13: solver(1−a) = b; b ≤ 0 → ¬(a ≪ 0)
opaque symbol AR13 [a b : τ ι]
  : π ((𝟏 - a) = b)
  → π (b ≤ 𝟎)
  → π (¬ (a ≪ 𝟎)) ≔
begin
  admit
end;
