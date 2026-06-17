// lemmas/ConjList.lp — derived facts about the snoc-list conjunction ⋀.
// Proved from B.lp's structural axioms (⋀_intro/⋀_init/⋀_last/⋀_nil_prf), the
// list operators, and propExt.
require open pp2lp.B;

// Re-add a conjunct at the front (the pushl end): PP's left-associative ∧ puts
// the key conjunct first, but the structural eliminators only touch the last.
// By induction, so it applies to an abstract ls where pushl is stuck.
opaque symbol ⋀_push_front (P : Prop)
  : Π ls : 𝕃* o, π P → π (⋀ ls) → π (⋀ (pushl P ls)) ≔
begin
  assume P;
  induction
  { assume hP hnil; refine hP }
  { assume ls' ih y hP hc;  // induction binds the IH before the element
    refine ⋀_intro (ih hP (⋀_init hc)) (⋀_last hc) }
end;

// Rebuild ⋀ L from its head (popl L) and the conjunction of its tail (⋀ (dropl L));
// the dual of the popl/dropl split, used by NRM20. popl/dropl branch on is_nil of
// the sub-list, so the induction re-generalises and case-splits it.
opaque symbol ⋀_pop_intro :
  Π L : 𝕃* o, π (popl L) → π (⋀ (dropl L)) → π (⋀ L) ≔
begin
  induction
  // L = ∎ : dropl ∎ ≡ ∎, so the tail hypothesis is π (⋀ ∎).
  { assume hpop htail; refine htail }
  // L = xs ∷ x : re-generalise and case-split xs to fire popl/dropl.
  { assume xs ih0 x;
    generalize xs;
    induction
    // xs = ∎ : singleton; popl L ≡ x ≡ ⋀ (∎ ∷ x).
    { assume ih x2 hpop htail; refine hpop }
    // xs = ys ∷ y : the outer IH recurses on the shorter sub-list.
    { assume ys rec y ih x2 hpop htail;
      refine ⋀_intro (ih hpop (⋀_init htail)) (⋀_last htail) } }
end;

// ---- Result-chain combinators ----

// conj_cons bridges the stuck `ite (is_nil p) …` of `conj (p ∷ q)` to `⋀ (p ∷ q)`
// (the is_nil guard is irreducible for abstract p). Both cases are reflexivity.
opaque symbol conj_cons (p : 𝕃* o) (q : Prop)
  : π (conj (p ∷ q) = ⋀ (p ∷ q)) ≔
begin
  induction
  { assume q; reflexivity }
  { assume p' ih x q; reflexivity }
end;

opaque symbol conj_snoc (qs : 𝕃* o) (y : Prop)
  : π (conj (qs ∷ y) = (conj qs ∧ y)) ≔
begin
  induction
  { assume y; refine eq_sym (⊤∧ y) }
  { assume qs' ih q y;
    rewrite conj_cons qs' q;
    refine propExt _ _ _ _
    { assume h; refine ∧ᵢ (⋀_init h) (⋀_last h) }
    { assume h; refine ⋀_intro (∧ₑ₁ h) (∧ₑ₂ h) } }
end;

// conj of a concat is the ∧ of the conjs — the equality the schema-2 `_1` rules
// use to combine two children's lists.
opaque symbol conj_concat_eq (l1 l2 : 𝕃* o)
  : π ((conj l1 ∧ conj l2) = conj (concat l1 l2)) ≔
begin
  assume l1;
  induction
  { refine ∧⊤ (conj l1) }
  { assume l2' ih y;
    have hL : π (conj (l2' ∷ y) = (conj l2' ∧ y)) { refine conj_snoc l2' y };
    have hR : π (conj (concat l1 (l2' ∷ y)) = (conj (concat l1 l2') ∧ y))
      { refine conj_snoc (concat l1 l2') y };
    rewrite hL;
    rewrite hR;
    rewrite left ih;
    refine eq_sym (∧_assoc (conj l1) (conj l2') y) }
end;

// ---- 2-element helpers ----
// A binary ∧ becomes ⋀ (∎ ∷ P ∷ Q); these replace ∧ᵢ / ∧ₑ₁ / ∧ₑ₂.

opaque symbol ⋀₂_intro [P Q : Prop]
  : π P → π Q → π (⋀ (∎ ∷ P ∷ Q)) ≔
begin
  assume P Q hP hQ;
  refine ⋀_intro (⋀_intro ⋀_nil_prf hP) hQ
end;

opaque symbol ⋀₂_hd [P Q : Prop]
  : π (⋀ (∎ ∷ P ∷ Q)) → π P ≔
begin
  assume P Q h;
  refine ⋀_init h           // ⋀_init h : π (⋀ (∎ ∷ P)) ≡ π P (singleton collapse)
end;

opaque symbol ⋀₂_snd [P Q : Prop]
  : π (⋀ (∎ ∷ P ∷ Q)) → π Q ≔
begin
  assume P Q h;
  refine ⋀_last h
end;
