require open
  pp2lp.B pp2lp.Eq;

symbol Hyp ≔ τ (list prd);
symbol dans ≔
  Stdlib.List.∈ prd_eq;
notation dans infix 5;

inductive Sqnt : TYPE ≔
  ⟝ : Hyp → Prd → Sqnt;
notation ⟝ infix 1;

injective symbol ▷ :
  Sqnt → TYPE;
symbol ⊩ (H : Hyp) (P : Prd)
  ≔ ▷ (H ⟝ P);
notation ⊩ infix 1;

symbol ⁇ (b : 𝔹) : TYPE
  ≔ π (istrue b);

// ---- Results ----
// Some PP rules produce an
// ancillary result predicate
// alongside their derivation.
// `Res Σ` is the type of
// result-derivations for
// sequent Σ. A value
// `ρ : Res Σ` encodes a proof
// of Σ together with a result
// predicate extractable via
// `obtain ρ`.
injective symbol Res :
  Sqnt → TYPE;
symbol result [Σ] :
  Prd → Res Σ;
symbol obtain [Σ] :
  Res Σ → Prd;
rule obtain (result $P) ↪ $P;

// Notational shorthand:
// Σ ⇝ R means "the proof of
// Σ gives result R".
symbol ⇝
  (Σ : Sqnt) (R : Prd)
  ≔ Res Σ;
notation ⇝ infix 1;
