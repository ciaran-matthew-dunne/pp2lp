// ConjList.lp — n-ary conjunction ⋀ over a snoc list 𝕃*.
//
// PP treats ∧ as left-associative, so the *last* conjunct is the most
// recently added — i.e. the outer constructor of a snoc list.  That makes
// PP's AND rules a single structural match on `ps ∷ P`:
//
//     init = ⋀ ps     last = P
//
// A conjunction is *always* `⋀ <list>`, never a native `∧`.  The four
// eliminators below are the complete (trusted) axiomatisation — no `∧`,
// no `⊤`, nothing to rewrite at any use site, so the singleton
// (`⋀ (∎ ∷ P) = P`) and nil (`⋀ ∎ = ⊤`) collapses never arise.

require open pp2lp.B;

// snoc-based list: grows on the right (∷), empty tail is ∎.
(a : Set) inductive 𝕃* : TYPE ≔
  | ∎ : 𝕃* a
  | ∷ : 𝕃* a → τ a → 𝕃* a;
notation ∷ infix left 5;


symbol list* : Set → Set;
rule τ (list* $a) ↪ 𝕃* $a;

symbol ite [a] : 𝔹 → τ a → τ a → τ a;
rule ite true $x _  ↪ $x
with ite false _ $y ↪ $y;

symbol is_nil [a] : 𝕃* a → 𝔹;
rule is_nil ∎       ↪ true
with is_nil (_ ∷ _) ↪ false;

// ⊤-valued elements are discharged conjuncts: PP drops them from its
// formulas, so result lists must drop them too or combined `res_tm`s
// diverge from PP's annotations (`⋀ (∎ ∷ ⊤ ∷ G)` has no erasure rule once
// the ⊤ is buried mid-list).  `mk_0` keeps ⊤ out of *leaf* lists; the two
// ⊤-rules catch ⊤s entering a *combine* (a sub-chain that discharged to
// ⊤, wrapped as a singleton element).  Every list is a leaf or a concat
// of two, so inductively no interior ⊤ survives.  Sound: conj of both
// sides stays propositionally equal (⊤ ∧ X ⟺ X).  Sequential: the
// ⊤-rules must take priority over the general cons rule.
sequential symbol concat [a] : 𝕃* a → 𝕃* a → 𝕃* a;
rule concat $xs ∎ ↪ $xs
with concat ∎ $ys ↪ $ys
with concat ($xs ∷ ⊤) $ys ↪ concat $xs $ys
with concat $xs ($ys ∷ ⊤) ↪ concat $xs $ys
with concat $xs ($ys ∷ $y) ↪ (concat $xs $ys) ∷ $y;

symbol dropl [a] : 𝕃* a → 𝕃* a;
rule dropl ∎          ↪ ∎
with dropl ($xs ∷ $x) ↪ ite (is_nil $xs) ∎ ((dropl $xs) ∷ $x);

symbol popl [a] : 𝕃* a → τ a;
rule popl ($xs ∷ $x) ↪ ite (is_nil $xs) $x (popl $xs);

symbol pushl [a] : τ a → 𝕃* a → 𝕃* a;
rule pushl $x ∎ ↪ (∎ ∷ $x)
with pushl $x ($ys ∷ $y) ↪ (pushl $x $ys) ∷ $y;

// n-ary conjunction.
injective symbol ⋀ : 𝕃* o → Prop;
notation ⋀ prefix 30;
rule ⋀ (∎ ∷ $p) ↪ $p
with ⋀ ($ps ∷ ⊤) ↪ ⋀ $ps;

// TODO. make non-sequential.
sequential symbol ⋀_snoc : Prop → Prop → Prop;
rule ⋀_snoc (⋀ $ps) $p ↪ ⋀ ($ps ∷ $p)
with ⋀_snoc $p $q ↪ ⋀ (∎ ∷ $p ∷ $q);

symbol conj : 𝕃* o → τ o;
rule conj ∎ ↪ ⊤
with conj ($p ∷ $q) ↪ ite (is_nil $p) ($q) (⋀ ($p ∷ $q));

injective symbol Res : τ o → TYPE;
symbol mk_res [t] (ts : 𝕃* o) : π (t = conj ts) → Res t;
symbol res_ts [t] (r : Res t) : 𝕃* o;
symbol res_eq [t] (r : Res t) : π (t = conj (res_ts r));
rule res_ts (mk_res $ts _)  ↪ $ts;
rule res_eq (mk_res _ $prf) ↪ $prf;

// Defined (not a pattern rule) so `res_tm r ≡ conj (res_ts r)` holds for a
// *variable* r too — passthrough `_1` rules rely on this conversion.
symbol res_tm [t] (r : Res t) : τ o ≔ conj (res_ts r);

// Singleton constructor — same signature as the old single-term `mk_1`,
// so every schema-0/1 (leaf / passthrough / single-result) `_1` rule keeps
// working verbatim: `conj (∎ ∷ x) ≡ x`, so `prf : π (t = x)` still fits.
// Only schema-2 combines build a real list (via `concat` + `mk_res`).
symbol mk_1 [t] (x : τ o) (prf : π (t = x)) : Res t ≔ mk_res (∎ ∷ x) prf;

// Empty-list constructor for *discharged* results (t = ⊤).  A discharged
// leaf contributes NOTHING to a combined result list: `concat`'s ∎ rules
// then erase it in any position, so a combined `res_tm` reduces to exactly
// PP's surviving conjuncts (PP drops discharged conjuncts).  The old
// `mk_1 ⊤` encoding put the ⊤ mid-list (`⋀ (∎ ∷ ⊤ ∷ G)`) where no ⋀ rule
// can erase it, so chain forms diverged from PP's formulas.
// `conj ∎ ↪ ⊤`, so the proof obligation is unchanged: π (t = ⊤).
symbol mk_0 [t] (prf : π (t = ⊤)) : Res t ≔ mk_res ∎ prf;


// ---- Axiomatisation: structural intro / eliminators ----
//
// `⋀_init`/`⋀_last` peel the snoc list one conjunct at a time and
// `⋀_intro` grows it; `⋀_nil_prf` is the empty conjunction.

symbol ⋀_nil_prf : π (⋀ ∎);
symbol ⋀_intro [ps : 𝕃* o] [P : Prop] : π (⋀ ps) → π P → π (⋀ (ps ∷ P));
symbol ⋀_init  [ps : 𝕃* o] [P : Prop] : π (⋀ (ps ∷ P)) → π (⋀ ps);
symbol ⋀_last  [ps : 𝕃* o] [P : Prop] : π (⋀ (ps ∷ P)) → π P;

// Head-intro: re-add a conjunct at the FRONT (`pushl` end).  The structural
// eliminators above only touch the *last* conjunct, but PP's left-associative
// ∧ puts the most significant conjunct (e.g. NRM20's `x = E`) *first* — at the
// head of the snoc list.  Derived from `⋀_intro`/`⋀_init`/`⋀_last` by induction,
// so it applies to an abstract `ls` where `pushl` is stuck.
opaque symbol ⋀_push_front (P : Prop)
  : Π ls : 𝕃* o, π P → π (⋀ ls) → π (⋀ (pushl P ls)) ≔
begin
  assume P;
  induction
  { assume hP hnil; refine hP }
  { assume ls' ih y hP hc;  // induction binds the IH *before* the element
    refine ⋀_intro (ih hP (⋀_init hc)) (⋀_last hc) }
end;

// Pop-front reconstruction: rebuild `⋀ L` from its head conjunct (`popl L`)
// and the conjunction of its tail (`⋀ (dropl L)`).  The dual of the popl/dropl
// split, used by NRM20 to reconstruct the full conjunction `⋀ (ps v)` after
// substituting the leading `x = E` conjunct.  Holds for non-empty L; the `∎`
// case is degenerate (its `popl ∎` hypothesis is vacuous) but provable since
// `dropl ∎ ≡ ∎`.  `popl`/`dropl` branch on `is_nil` of the *sub*-list, so the
// snoc induction must re-generalise and case-split that sub-list.
opaque symbol ⋀_pop_intro :
  Π L : 𝕃* o, π (popl L) → π (⋀ (dropl L)) → π (⋀ L) ≔
begin
  induction
  // L = ∎ : dropl ∎ ≡ ∎, so the tail hypothesis *is* π (⋀ ∎).
  { assume hpop htail; refine htail }
  // L = xs ∷ x : popl/dropl branch on `is_nil xs`, so re-generalise and
  // case-split xs to fire those rules.
  { assume xs ih0 x;
    generalize xs;
    induction
    // xs = ∎ : L = ∎ ∷ x is a singleton; popl L ≡ x ≡ ⋀ (∎ ∷ x).
    { assume ih x2 hpop htail; refine hpop }
    // xs = ys ∷ y : popl L ≡ popl (ys∷y), dropl L ≡ dropl (ys∷y) ∷ x; the
    // re-bound outer IH does the recursion on the shorter sub-list.
    { assume ys rec y ih x2 hpop htail;
      refine ⋀_intro (ih hpop (⋀_init htail)) (⋀_last htail) } }
end;

// ---- Result-chain combinators ----
//
// `conj` of a snoc decomposes into init-conj ∧ last; `concat` of two
// conjunct lists is the ∧ of their conjs.  `conj_concat_eq` is the
// equality the schema-2 `_1` rules use to combine two children's lists.

symbol conj_snoc (qs : 𝕃* o) (y : Prop)
  : π (conj (qs ∷ y) = (conj qs ∧ y));
//begin
//  induction
//  { assume y; refine eq_sym (⊤∧ y) }
//  { assume qs' q _ih y;
//    refine propExt _ _ _ _
//    { assume h; refine ∧ᵢ (⋀_init h) (⋀_last h) }
//    { assume h; refine ⋀_intro (∧ₑ₁ h) (∧ₑ₂ h) } }
//end;

symbol conj_concat_eq (l1 l2 : 𝕃* o)
  : π ((conj l1 ∧ conj l2) = conj (concat l1 l2));
//begin
//  assume l1;
//  induction
//  { refine ∧⊤ (conj l1) }
//  { assume l2' ih y;
//    have hL : π (conj (l2' ∷ y) = (conj l2' ∧ y)) { refine conj_snoc l2' y };
//    have hR : π (conj (concat l1 (l2' ∷ y)) = (conj (concat l1 l2') ∧ y))
//      { refine conj_snoc (concat l1 l2') y };
//    rewrite hL;
//    rewrite hR;
//    rewrite left ih;
//    refine eq_sym (∧_assoc (conj l1) (conj l2') y) }
//end;

// ---- 2-element helpers ----
//
// PP's NRM/AXM/EQ rules whose shape is a binary `∧` become `⋀ (∎ ∷ P ∷ Q)`.
// `⋀₂_intro` replaces `∧ᵢ`, `⋀₂_hd` replaces `∧ₑ₁`, `⋀₂_snd` replaces `∧ₑ₂`.
// All three are pure snoc-list surgery — no singleton collapse needed:
// `⋀₂_hd` peels Q off with ⋀_init, then P off the remainder with ⋀_last.

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
