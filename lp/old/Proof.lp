require open pp2lp.Syntax;

// ------ Sequents ---------------------------

// set-code for sequents.
symbol seq : Set;

// infix data constructor for sequents.
injective symbol ⟝ : El (list prd ⤳ prd ⤳ seq);
notation ⟝ infix 0;

// primitive type constructor for sequent deriviation.
injective symbol ✓ : El bool → El seq → TYPE;

// 'standard' sequent derivation is defined as a special case.
injective symbol ▷ : El seq → TYPE ≔ λ Σ, ✓ true Σ;

// `Thm p` is the type of derivations of `(nil ⟝ p)`.
injective symbol Thm : El prd → TYPE ≔ λ p, ▷ (nil ⟝ p);

// ---- Results ------------------------------
// some rules in the pp docs have side conditions involving a
// binary relation `⟿` between sequents and predicates.

// some rules in the pp docs have a consequent `Σ` and a 'resultat' `R`,
// and sometimes side conditions which may involve `⟿`.
//  we view such a rule as providing a "derivation" of `Σ ⟿ R`.

// for a sequent `Σ`, we define `Res Σ` as the 'type of result derivations` for `Σ`.
// if `ρ : Res Σ`, then `ρ` encodes some proof of `Σ ⟿ R` for some `R`.
injective symbol Res : El seq → TYPE;

// `result [Σ] P` is an 'axiomatic' derivation of `Σ ⟿ R`.
symbol result [Σ : El seq] : El prd → Res Σ;

// `obtain [Σ] ρ` returns the predicate `R` derived by `ρ`.
symbol obtain [Σ : El seq] : Res Σ → El prd;

// `obtain` is the inverse of `result`.
rule obtain (result $P) ↪ $P;

// abuse of notation: coerce result-derivations to their obtained predicates.
coerce_rule coerce (Res $Σ) (El prd) $ρ ↪ obtain $ρ;
