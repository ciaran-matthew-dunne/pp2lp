// ConjList.lp — Abstract n-ary conjunction ⋀ over 𝕃 o

require open Stdlib.Set Stdlib.Prop Stdlib.Eq
            Stdlib.List Stdlib.Impred;

injective symbol ⋀ : 𝕃 o → Prop;

notation ⋀ prefix 30;

// ---- init/last decomposition (proposition-level) ----

// ⋀_init_list : list-level init (all but last)
symbol ⋀_init_list : 𝕃 o → 𝕃 o;
rule ⋀_init_list (_ ⸬ □) ↪ □
with ⋀_init_list ($x ⸬ $y ⸬ $rest) ↪ $x ⸬ ⋀_init_list ($y ⸬ $rest);

// ⋀_init : proposition-level init — collapses singletons
symbol ⋀_init : τ o → τ o;
rule ⋀_init (⋀ ($x ⸬ $y ⸬ □)) ↪ $x;
rule ⋀_init (⋀ ($x ⸬ $y ⸬ $z ⸬ $rest))
  ↪ ⋀ ($x ⸬ ⋀_init_list ($y ⸬ $z ⸬ $rest));

// ---- Eliminators for init/last decomposition ----

symbol ⋀_front [ps : 𝕃 o] : π (⋀ ps) → π (⋀_init (⋀ ps));
symbol ⋀_back  [ps : 𝕃 o] : π (⋀ ps) → π (last ⊤ ps);
symbol ⋀_rejoin [ps : 𝕃 o] : π (⋀_init (⋀ ps)) → π (last ⊤ ps) → π (⋀ ps);

// ---- Split equality: ⋀ ps = ⋀_init(⋀ ps) ∧ last(⊤, ps) ----

symbol ⋀_split [ps : 𝕃 o]
  : π (⋀ ps = (⋀_init (⋀ ps) ∧ last ⊤ ps));

// ---- Equalities (apply via `rewrite` in rule proofs) ----

symbol ⋀_nil  : π (⋀ □ = ⊤);
symbol ⋀_one  (P : Prop) : π (⋀ (P ⸬ □) = P);
symbol ⋀_cons (P : Prop) (rest : 𝕃 o)
  : π (⋀ (P ⸬ rest) = (P ∧ ⋀ rest));

// ---- Derived equalities ----

opaque symbol ⋀_bin (P Q : Prop)
  : π (⋀ (P ⸬ Q ⸬ □) = (P ∧ Q)) ≔
begin
  assume P Q;
  rewrite ⋀_cons P (Q ⸬ □);
  rewrite ⋀_one Q;
  reflexivity
end;

// ---- Eliminators / introduction ----

symbol ⋀_hd (P : Prop) (rest : 𝕃 o)
  : π (⋀ (P ⸬ rest)) → π P;
symbol ⋀_tl (P : Prop) (rest : 𝕃 o)
  : π (⋀ (P ⸬ rest)) → π (⋀ rest);
symbol ⋀_intro (P : Prop) (rest : 𝕃 o)
  : π P → π (⋀ rest) → π (⋀ (P ⸬ rest));

// ---- Nil proof (base case for ⋀_intro chains) ----

opaque symbol ⋀_nil_prf : π (⋀ □) ≔
begin
  rewrite ⋀_nil;
  refine ⊤ᵢ
end;
