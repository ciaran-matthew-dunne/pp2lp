// Res.lp — helpers shared by the per-rule `_1` (Result) variants.
//
// Each `_1` rule lives in its own topic file (Conj.lp, Disj.lp, …);
// this file collects the cross-cutting infrastructure they share:
//
//   - generic equality combinators (eq_trans, conj_eq, ∧_assoc, …)
//   - per-connective equality lemmas (and1_eq, or1_eq, …) — these are
//     just propositional facts about the connective transformations
//     specified by §A of the PP rule reference
//   - special bridges (opr1_eq, opr2_eq, xst7_eq, xst8_eq, nrm1_eq)
//
// The `Res`, `mk_1`, `res_tm`, `res_eq` primitives themselves live in
// Quant.lp so that All.lp / Xst.lp can refer to them.

require open pp2lp.B pp2lp.lemmas.Int pp2lp.lemmas.ConjList pp2lp.lemmas.Tuple;

// ============================================================
// Generic equality combinators
// ============================================================

opaque symbol eq_trans [a] [P Q R : τ a]
  : π (P = Q) → π (Q = R) → π (P = R) ≔
begin assume a P Q R h1 h2; rewrite h1; refine h2 end;

// Transport a `Res` along a propositional equality of its statement: given
// `a = b` and a `Res b`, build a `Res a`.  The emitter uses this to re-order
// the conjuncts a chain `_1` form leaves at the tail (e.g. NRM20_1's pinning
// equality) back to the position PP's goal carries them, *without* duplicating
// the (large) underlying chain term across `res_tm`/`res_eq`.
symbol res_cong [a b : τ o] (h : π (a = b)) (r : Res b) : Res a
  ≔ mk_1 (res_tm r) (eq_trans h (res_eq r));

// A true proposition equals ⊤.  This is the Schema-0 result bridge
// (§8.13): a rule "sans antécédent véritable" produces the result VRAI,
// which the spec requires to be *equivalent to the consequent P* — here
// modulo the hypotheses H that license the rule's side-condition.  Given
// a proof of P (the hyp the rule looked up), `propExt` discharges `P = ⊤`.
opaque symbol prop_eq_top [P : Prop] (hp : π P) : π (P = ⊤) ≔
begin
  assume P hp;
  refine propExt _ _ _ _
  { assume h; refine ⊤ᵢ }
  { assume h; refine hp }
end;

// ¬⊤ = ⊥, as a propositional equality (for VR2_1's Schema-1 passthrough).
opaque symbol not_top_eq_bot : π ((¬ ⊤) = ⊥) ≔
begin
  refine propExt _ _ _ _
    { assume h; refine h ⊤ᵢ }
    { assume h; refine ⊥ₑ h }
end;

// Equality is commutative, as a propositional equality (for BOOL21/22_1).
opaque symbol eq_comm_prop [a] (x y : τ a) : π ((x = y) = (y = x)) ≔
begin
  assume a x y;
  refine propExt _ _ (λ h, eq_sym h) (λ h, eq_sym h)
end;

// ¬¬A = A (classical) — for the XST51/61_1 double-negation passthroughs.
opaque symbol not_not_eq [A : Prop] : π ((¬ ¬ A) = A) ≔
begin assume A; refine propExt _ _ (λ h, ¬¬ₑ A h) (λ h hn, hn h) end;

// (¬⊥ ⇒ R) = R — ¬⊥ is provable, so the antecedent drops (FX1_1).
opaque symbol not_bot_imp_eq [R : Prop] : π ((¬ ⊥ ⇒ R) = R) ≔
begin assume R; refine propExt _ _ (λ h, h (λ b, b)) (λ hr _, hr) end;

// ⋀(∎ ∷ X ∷ Y) = (X ∧ Y) — the 2-element snoc conjunction is binary ∧ (EQC2_1).
opaque symbol conj2_eq [X Y : Prop] : π ((⋀ (∎ ∷ X ∷ Y)) = (X ∧ Y)) ≔
begin
  assume X Y;
  refine propExt _ _
    (λ h, ∧ᵢ (⋀₂_hd h) (⋀₂_snd h))
    (λ h, ⋀₂_intro (∧ₑ₁ h) (∧ₑ₂ h))
end;

// (a↦b)=(c↦d) = (a=c ∧ b=d) — pair injectivity (EQC1/2_1).
opaque symbol pair_eq_decomp [a b c d : τ ι]
  : π (((a ↦ b) = (c ↦ d)) = ((a = c) ∧ (b = d))) ≔
begin
  assume a b c d;
  refine propExt _ _
    (λ h, pair_inj a b c d h)
    (λ h, pair_cong a b c d (∧ₑ₁ h) (∧ₑ₂ h))
end;

// Conj congruence: lift independent equalities to their conjunction.
opaque symbol conj_eq [A B S1 S2 : Prop]
  : π (A = S1) → π (B = S2) → π ((A ∧ B) = (S1 ∧ S2)) ≔
begin
  assume A B S1 S2 h1 h2;
  rewrite h1; rewrite h2; reflexivity
end;

// Conj associativity (right ↔ left), used by ALL7/XST8 continuations
// when the inner _1 chain produced a right-assoc conjunction.
opaque symbol ∧_assoc [A B C : Prop]
  : π ((A ∧ (B ∧ C)) = ((A ∧ B) ∧ C)) ≔
begin
  assume A B C;
  refine propExt _ _ _ _
  { assume h; refine ∧ᵢ (∧ᵢ (∧ₑ₁ h) (∧ₑ₁ (∧ₑ₂ h))) (∧ₑ₂ (∧ₑ₂ h)) }
  { assume h; refine ∧ᵢ (∧ₑ₁ (∧ₑ₁ h)) (∧ᵢ (∧ₑ₂ (∧ₑ₁ h)) (∧ₑ₂ h)) }
end;

// Antecedent equivalence → implication equality (for AND5_1).
opaque symbol ante_cong [C C' R : Prop]
  : (π C → π C') → (π C' → π C) → π ((C ⇒ R) = (C' ⇒ R)) ≔
begin
  assume C C' R fwd bwd;
  refine propExt _ _ _ _
    { assume h hc'; refine h (bwd hc') }
    { assume h hc; refine h (fwd hc) }
end;

// Implication right congruence.
opaque symbol imp_cong_r [P Q R : Prop]
  : π (Q = R) → π ((P ⇒ Q) = (P ⇒ R)) ≔
begin assume P Q R h; rewrite h; reflexivity end;

// Implication right congruence *under the antecedent*: the consequent
// equality may consume π P.  This re-binds the antecedent a chain-local
// AXM3_1 consumed, making the equality of the whole node unconditional —
// the mechanism behind IMP4_1U (Impl.lp), which threads the IMP4'
// hypothesis to its child chain.
opaque symbol imp_cong_r_under [P Q R : Prop]
  (h : π P → π (Q = R)) : π ((P ⇒ Q) = (P ⇒ R)) ≔
begin
  assume P Q R h;
  refine propExt _ _ _ _
  { assume f hp; refine =⇒ (h hp) (f hp) }
  { assume f hp; refine =⇒ (eq_sym (h hp)) (f hp) }
end;

// Implication left congruence.
opaque symbol imp_cong_l [P P' Q : Prop]
  : π (P = P') → π ((P ⇒ Q) = (P' ⇒ Q)) ≔
begin assume P P' Q h; rewrite h; reflexivity end;

// Negation congruence.
opaque symbol not_cong [A B : Prop]
  : π (A = B) → π ((¬ A) = (¬ B)) ≔
begin assume A B h; rewrite h; reflexivity end;

// Snoc-list last-element congruence: rewrite the final conjunct of a `⋀`.
opaque symbol conj_snoc_last_cong [ps : 𝕃* o] [P Q : Prop]
  : π (P = Q) → π (⋀ (ps ∷ P) = ⋀ (ps ∷ Q)) ≔
begin assume ps P Q h; rewrite h; reflexivity end;

// Swap the last two conjuncts.  With [conj_init_cong] below this bubbles a
// conjunct to the end of the list — the emitter rotates an NRM20/21 pinning
// equality into tail position before applying the tail-form lemmas.
opaque symbol conj_swap_last2 [ps : 𝕃* o] [P Q : Prop]
  : π (⋀ (ps ∷ P ∷ Q) = ⋀ (ps ∷ Q ∷ P)) ≔
begin
  assume ps P Q;
  refine propExt _ _ _ _
  { assume h;
    refine ⋀_intro (⋀_intro (⋀_init (⋀_init h)) (⋀_last h))
                   (⋀_last (⋀_init h)) }
  { assume h;
    refine ⋀_intro (⋀_intro (⋀_init (⋀_init h)) (⋀_last h))
                   (⋀_last (⋀_init h)) }
end;

// Init congruence: rewrite everything *below* the last conjunct.
opaque symbol conj_init_cong [ps qs : 𝕃* o] [P : Prop]
  : π (⋀ ps = ⋀ qs) → π (⋀ (ps ∷ P) = ⋀ (qs ∷ P)) ≔
begin
  assume ps qs P h;
  refine propExt _ _ _ _
  { assume hc; refine ⋀_intro (=⇒ h (⋀_init hc)) (⋀_last hc) }
  { assume hc; refine ⋀_intro (=⇒ (eq_sym h) (⋀_init hc)) (⋀_last hc) }
end;

// Strip a known antecedent: π P → ((P ⇒ Q) = Q).
opaque symbol imp_known_drop [P Q : Prop]
  : π P → π ((P ⇒ Q) = Q) ≔
begin
  assume P Q hp;
  refine propExt _ _ _ _
  { assume hpq; refine hpq hp }
  { assume hq hp2; refine hq }
end;

// LHS-of-leq-zero congruence (for AR9_1).
opaque symbol leq_zero_eq [E F : τ ι]
  : π (E = F) → π ((leq E 𝟎) = (leq F 𝟎)) ≔
begin assume E F h; rewrite h; reflexivity end;

// Equality / ≤ congruence on both operands — the propositional equality
// `(a ⋈ c) = (b ⋈ d)` from value equalities `a = b`, `c = d`.  Used by AR10's
// non-trivial solver step, where PP normalises an arithmetic atom inside a
// `=`/`≤` predicate (e.g. `-(-x) = x` ↦ `x = x`); [Arith_proofs.prove_pred_eq]
// supplies the operand proofs from the reflective normaliser.
opaque symbol eq_cong [a b c d : τ ι]
  : π (a = b) → π (c = d) → π ((a = c) = (b = d)) ≔
begin assume a b c d h1 h2; rewrite h1; rewrite h2; reflexivity end;

opaque symbol leq_cong [a b c d : τ ι]
  : π (a = b) → π (c = d) → π ((leq a c) = (leq b d)) ≔
begin assume a b c d h1 h2; rewrite h1; rewrite h2; reflexivity end;

// Membership congruence: `(a ϵ S) = (b ϵ T)` from `a = b`, `S = T`.  AR10's
// solver step also fires inside a *membership* predicate (`s9(x+1) : s10` ↦
// `s9(1+x) : s10`), where the normalised atom sits under a function image.
opaque symbol mem_cong [a b S T : τ ι]
  : π (a = b) → π (S = T) → π ((a ϵ S) = (b ϵ T)) ≔
begin assume a b S T h1 h2; rewrite h1; rewrite h2; reflexivity end;

// Expression-level congruence for the compound atoms PP's arithmetic normaliser
// rewrites *through* (the differing leaf is buried under a function image / pair,
// so the whole `=`/`≤`/`ϵ` operand is not itself a linear term and the reflective
// normaliser must recurse): function application on the argument ([eapp_arg_cong])
// and on both head and argument ([eapp_cong], for a non-symbol head r~(·)),
// pairing, and the `+`/`−`/neg arithmetic constructors.
opaque symbol eapp_arg_cong [f a b : τ ι]
  : π (a = b) → π (eapp f a = eapp f b) ≔
begin assume f a b h; rewrite h; reflexivity end;

opaque symbol eapp_cong [f g a b : τ ι]
  : π (f = g) → π (a = b) → π (eapp f a = eapp g b) ≔
begin assume f g a b h1 h2; rewrite h1; rewrite h2; reflexivity end;

opaque symbol maplet_cong [a b c d : τ ι]
  : π (a = b) → π (c = d) → π ((a ↦ c) = (b ↦ d)) ≔
begin assume a b c d h1 h2; rewrite h1; rewrite h2; reflexivity end;

opaque symbol plus_cong [a b c d : τ ι]
  : π (a = b) → π (c = d) → π (plus a c = plus b d) ≔
begin assume a b c d h1 h2; rewrite h1; rewrite h2; reflexivity end;

opaque symbol minus_cong [a b c d : τ ι]
  : π (a = b) → π (c = d) → π (minus a c = minus b d) ≔
begin assume a b c d h1 h2; rewrite h1; rewrite h2; reflexivity end;

opaque symbol neg_cong [a b : τ ι]
  : π (a = b) → π (neg a = neg b) ≔
begin assume a b h; rewrite h; reflexivity end;

// ============================================================
// Per-connective equality lemmas (§A.1–A.5, A.13)
//
// The AND lemmas decompose the snoc conjunction `⋀ (ps ∷ P)` into init
// `⋀ ps` and last `P`.  Proved directly from the ConjList eliminators:
// build the conjunction with `⋀_intro hps hp` and destruct it with
// `⋀_init`/`⋀_last`, in place of the `∧ᵢ`/`∧ₑ₁`/`∧ₑ₂` of the OR/IMP lemmas.
// ============================================================

// AND1: (¬⋀(ps∷P)⇒R) = ((¬P⇒R) ∧ (¬⋀ps⇒R))   [last-first]
opaque symbol and1_eq [ps : 𝕃* o] [P R : Prop]
  : π ((¬ ⋀ (ps ∷ P) ⇒ R) = ((¬ P ⇒ R) ∧ (¬ ⋀ ps ⇒ R))) ≔
begin
  assume ps P R;
  refine propExt _ _ _ _
    { assume h; refine ∧ᵢ
        (λ hnp, h (λ hand, hnp (⋀_last hand)))
        (λ hni, h (λ hand, hni (⋀_init hand))) }
    { assume h hnand;
      have hnand2 : π (¬ (⋀ ps ∧ P))
        { assume hand; refine hnand (⋀_intro (∧ₑ₁ hand) (∧ₑ₂ hand)) };
      have hor : π (¬ ⋀ ps ∨ ¬ P)
        { refine =⇒ (deMorgan_∧ (⋀ ps) P) hnand2 };
      refine ∨ₑ hor _ _
        { assume hni; refine ∧ₑ₂ h hni }
        { assume hnp; refine ∧ₑ₁ h hnp } }
end;

// AND2: ¬⋀(ps∷P) = (⋀ps ⇒ ¬P)
opaque symbol and2_eq [ps : 𝕃* o] [P : Prop]
  : π (¬ ⋀ (ps ∷ P) = (⋀ ps ⇒ ¬ P)) ≔
begin
  assume ps P;
  refine propExt _ _ _ _
    { assume h hps hp; refine h (⋀_intro hps hp) }
    { assume h hand; refine h (⋀_init hand) (⋀_last hand) }
end;

// AND3: (⋀(ps∷P)⇒R) = (⋀ps ⇒ (P⇒R))
opaque symbol and3_eq [ps : 𝕃* o] [P R : Prop]
  : π ((⋀ (ps ∷ P) ⇒ R) = (⋀ ps ⇒ (P ⇒ R))) ≔
begin
  assume ps P R;
  refine propExt _ _ _ _
    { assume h hps hp; refine h (⋀_intro hps hp) }
    { assume h hand; refine h (⋀_init hand) (⋀_last hand) }
end;

// AND4: ⋀(ps∷P) = (P ∧ ⋀ps)   [last-first reordering for AND4_1]
opaque symbol and4_eq [ps : 𝕃* o] [P : Prop]
  : π (⋀ (ps ∷ P) = (P ∧ ⋀ ps)) ≔
begin
  assume ps P;
  refine propExt _ _ _ _
    { assume h; refine ∧ᵢ (⋀_last h) (⋀_init h) }
    { assume h; refine ⋀_intro (∧ₑ₂ h) (∧ₑ₁ h) }
end;

// OR1: ¬(P∨Q)⇒R = (¬P⇒¬Q⇒R)
opaque symbol or1_eq [P Q R : Prop]
  : π ((¬ (P ∨ Q) ⇒ R) = (¬ P ⇒ (¬ Q ⇒ R))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h1 hnp hnq;
      have hnpq : π (¬ (P ∨ Q))
        { assume hpq; refine ∨ₑ hpq _ _
          { assume hp; refine hnp hp }
          { assume hq; refine hnq hq } };
      refine h1 hnpq }
    { assume h1 hnpq;
      have hnpnq : π (¬ P ∧ ¬ Q) { refine =⇒ (deMorgan_∨ P Q) hnpq };
      refine h1 (∧ₑ₁ hnpnq) (∧ₑ₂ hnpnq) }
end;

// OR2: ¬(P∨Q) = (¬Q ∧ ¬P)
opaque symbol or2_eq [P Q : Prop]
  : π (¬ (P ∨ Q) = (¬ Q ∧ ¬ P)) ≔
begin
  assume P Q;
  rewrite deMorgan_∨;
  rewrite ∧_com;
  reflexivity
end;

// OR3: (P∨Q)⇒R = (Q⇒R) ∧ (P⇒R)
opaque symbol or3_eq [P Q R : Prop]
  : π (((P ∨ Q) ⇒ R) = ((Q ⇒ R) ∧ (P ⇒ R))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h; refine ∧ᵢ (λ hq, h (∨ᵢ₂ hq)) (λ hp, h (∨ᵢ₁ hp)) }
    { assume h hpq; refine ∨ₑ hpq _ _
      { assume hp; refine ∧ₑ₂ h hp }
      { assume hq; refine ∧ₑ₁ h hq } }
end;

// OR4: P∨Q = (¬P⇒Q). P, Q explicit to avoid HO-unification issues.
opaque symbol or4_eq (P Q : Prop)
  : π ((P ∨ Q) = (¬ P ⇒ Q)) ≔
begin
  assume P Q;
  refine propExt _ _ _ _
    { assume hpq hnp; refine ∨ₑ hpq _ _
      { assume hp; refine ⊥ₑ (hnp hp) }
      { assume hq; refine hq } }
    { assume h1; refine ∨ₑ (em P) _ _
      { assume hp; refine ∨ᵢ₁ hp }
      { assume hnp; refine ∨ᵢ₂ (h1 hnp) } }
end;

// IMP1: ¬(P⇒Q)⇒R = (P⇒¬Q⇒R)
opaque symbol imp1_eq [P Q R : Prop]
  : π ((¬ (P ⇒ Q) ⇒ R) = (P ⇒ (¬ Q ⇒ R))) ≔
begin
  assume P Q R;
  rewrite ¬⇒=∧¬;
  refine propExt _ _ _ _
    { assume h1 hp hnq; refine h1 (∧ᵢ hp hnq) }
    { assume h1 h2; refine h1 (∧ₑ₁ h2) (∧ₑ₂ h2) }
end;

// IMP2: ¬(P⇒Q) = (¬Q ∧ P)
opaque symbol imp2_eq [P Q : Prop]
  : π (¬ (P ⇒ Q) = (¬ Q ∧ P)) ≔
begin
  assume P Q;
  rewrite ¬⇒=∧¬;
  rewrite ∧_com;
  reflexivity
end;

// IMP3: (P⇒Q)⇒R = (Q⇒R) ∧ (¬P⇒R)
opaque symbol imp3_eq [P Q R : Prop]
  : π (((P ⇒ Q) ⇒ R) = ((Q ⇒ R) ∧ (¬ P ⇒ R))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h; refine ∧ᵢ
      (λ hq, h (λ h0, hq))
      (λ hnp, h (λ hp, ⊥ₑ (hnp hp))) }
    { assume h hpq; refine ∨ₑ (em P) _ _
      { assume hp; refine ∧ₑ₁ h (hpq hp) }
      { assume hnp; refine ∧ₑ₂ h hnp } }
end;

// EQV1: ¬(P⇔Q)⇒R = (P⇒¬Q⇒R) ∧ (¬P⇒Q⇒R)
opaque symbol eqv1_eq [P Q R : Prop]
  : π ((¬ (P ⇔ Q) ⇒ R) = ((P ⇒ (¬ Q ⇒ R)) ∧ (¬ P ⇒ (Q ⇒ R)))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h; refine ∧ᵢ
      (λ hp hnq, h (λ heqv, hnq (∧ₑ₁ heqv hp)))
      (λ hnp hq, h (λ heqv, hnp (∧ₑ₂ heqv hq))) }
    { assume h hneqv;
      refine ∨ₑ (em P) _ _
      { assume hp; refine ∨ₑ (em Q) _ _
        { assume hq;
          have heqv : π (P ⇔ Q) { refine ∧ᵢ (λ h0, hq) (λ h0, hp) };
          refine ⊥ₑ (hneqv heqv) }
        { assume hnq; refine ∧ₑ₁ h hp hnq } }
      { assume hnp; refine ∨ₑ (em Q) _ _
        { assume hq; refine ∧ₑ₂ h hnp hq }
        { assume hnq;
          have heqv : π (P ⇔ Q)
            { refine ∧ᵢ (λ hp, ⊥ₑ (hnp hp)) (λ hq, ⊥ₑ (hnq hq)) };
          refine ⊥ₑ (hneqv heqv) } } }
end;

// EQV2: ¬(P⇔Q) = (P⇒¬Q) ∧ (¬Q⇒P)
opaque symbol eqv2_eq [P Q : Prop]
  : π (¬ (P ⇔ Q) = ((P ⇒ ¬ Q) ∧ (¬ Q ⇒ P))) ≔
begin
  assume P Q;
  refine propExt _ _ _ _
    { assume hneqv;
      refine ∧ᵢ
        (λ hp hq,
          hneqv (∧ᵢ (λ h0, hq) (λ h0, hp)))
        (λ hnq, ¬¬ₑ P (λ hnp,
          hneqv (∧ᵢ (λ hp, ⊥ₑ (hnp hp)) (λ hq, ⊥ₑ (hnq hq))))) }
    { assume hand heqv;
      refine ∨ₑ (em Q) _ _
        { assume hq; refine ∧ₑ₁ hand (∧ₑ₂ heqv hq) hq }
        { assume hnq;
          have hp : π P { refine ∧ₑ₂ hand hnq };
          have hq : π Q { refine ∧ₑ₁ heqv hp };
          refine hnq hq } }
end;

// EQV3: (P⇔Q)⇒R = (P⇒Q⇒R) ∧ (¬P⇒¬Q⇒R)
opaque symbol eqv3_eq [P Q R : Prop]
  : π (((P ⇔ Q) ⇒ R) = ((P ⇒ (Q ⇒ R)) ∧ (¬ P ⇒ (¬ Q ⇒ R)))) ≔
begin
  assume P Q R;
  refine propExt _ _ _ _
    { assume h; refine ∧ᵢ
      (λ hp hq, h (∧ᵢ (λ h0, hq) (λ h0, hp)))
      (λ hnp hnq, h (∧ᵢ
        (λ hp, ⊥ₑ (hnp hp))
        (λ hq, ⊥ₑ (hnq hq)))) }
    { assume h heqv;
      refine ∨ₑ (em P) _ _
      { assume hp;
        have hq : π Q { refine ∧ₑ₁ heqv hp };
        refine ∧ₑ₁ h hp hq }
      { assume hnp;
        refine ∨ₑ (em Q) _ _
        { assume hq;
          have hp : π P { refine ∧ₑ₂ heqv hq };
          refine ⊥ₑ (hnp hp) }
        { assume hnq; refine ∧ₑ₂ h hnp hnq } } }
end;

// EQV4: (P⇔Q) = (P⇒Q) ∧ (Q⇒P). Definitional in stdlib (⇔ ≔ λp q, …).
opaque symbol eqv4_eq [P Q : Prop]
  : π ((P ⇔ Q) = ((P ⇒ Q) ∧ (Q ⇒ P))) ≔
begin assume P Q; reflexivity end;

// NOT1: ¬¬P⇒R = (P⇒R)
opaque symbol not1_eq [P R : Prop]
  : π ((¬ ¬ P ⇒ R) = (P ⇒ R)) ≔
begin
  assume P R;
  refine propExt _ _ _ _
    { assume h1 hp; refine h1 (λ hnp, hnp hp) }
    { assume h1 hnnp; refine h1 (¬¬ₑ P hnnp) }
end;

// EVR3: (E=E)⇒P = P
opaque symbol evr3_eq [E : τ ι] [P : Prop]
  : π (((E = E) ⇒ P) = P) ≔
begin
  assume E P;
  refine propExt _ _ _ _
    { assume h1; refine h1 (eq_refl E) }
    { assume h1 h2; refine h1 }
end;

// ============================================================
// Special bridges (OPR1/OPR2, XST7/XST8, NRM1)
// ============================================================

// OPR1 bridge: (x=E ⇒ P x) = (x=E ⇒ P E). Holds pointwise: when x=E
// is true, both sides reduce to P E; when false, both are vacuously ⊤.
opaque symbol opr1_eq [E : τ ι] (P : τ ι → Prop) (x : τ ι)
  : π ((x = E ⇒ P x) = (x = E ⇒ P E)) ≔
begin
  assume E P x;
  refine propExt _ _ _ _
    { assume hyp hxe; have px : π (P x) { refine hyp hxe };
      rewrite left hxe; refine px }
    { assume hyp hxe; have pe : π (P E) { refine hyp hxe };
      rewrite hxe; refine pe }
end;

// OPR2 bridge: (E=x ⇒ P x) = (E=x ⇒ P E).
opaque symbol opr2_eq [E : τ ι] (P : τ ι → Prop) (x : τ ι)
  : π ((E = x ⇒ P x) = (E = x ⇒ P E)) ≔
begin
  assume E P x;
  refine propExt _ _ _ _
    { assume hyp hex; have px : π (P x) { refine hyp hex };
      rewrite hex; refine px }
    { assume hyp hex; have pe : π (P E) { refine hyp hex };
      rewrite left hex; refine pe }
end;

// XST7: ((∃-block, P) ⇒ R) = (∀-block, P ⇒ R)
opaque symbol xst7_eq [n] [P : Tuple n → Prop] [R : Prop]
  : π (((`?? v, P v) ⇒ R) = (`!! v, P v ⇒ R)) ≔
begin
  assume n P R;
  refine propExt _ _ _ _
    { assume hir; refine pi_to_!! _
        (λ v hPv, hir (pi_to_??_intro P v hPv)) }
    { assume hall hex; refine pi_to_??_elim P
        (λ v hpv, !!_to_pi (λ v, P v ⇒ R) hall v hpv) hex }
end;

// XST6: ¬(∃-block, P) = (∀-block, ¬P)  (quantifier De Morgan).
opaque symbol xst6_eq [n] [P : Tuple n → Prop]
  : π ((¬ (`?? v, P v)) = (`!! v, ¬ (P v))) ≔
begin
  assume n P;
  refine propExt _ _ _ _
    { assume hne; refine pi_to_!! (λ v, ¬ (P v))
        (λ v hpv, hne (pi_to_??_intro P v hpv)) }
    { assume hall hex; refine pi_to_??_elim P
        (λ v hpv, !!_to_pi (λ v, ¬ (P v)) hall v hpv) hex }
end;

// XST61: ¬(∃v·¬P v) = (∀v·P v) — quantifier De Morgan then double negation.
opaque symbol xst61_eq [n] [P : Tuple n → Prop]
  : π ((¬ (`?? v, ¬ (P v))) = (`!! v, P v)) ≔
begin
  assume n P;
  refine eq_trans xst6_eq (!!_cong (λ v, not_not_eq))
end;

// XST8: (∃-block, P) = ((∀-block, ¬P) ⇒ ⊥)
opaque symbol xst8_eq [n] [P : Tuple n → Prop]
  : π ((`?? v, P v) = ((`!! v, ¬ (P v)) ⇒ ⊥)) ≔
begin
  assume n P;
  refine propExt _ _ _ _
    { assume hex hall; refine pi_to_??_elim P
        (λ v hpv, !!_to_pi (λ v, ¬ (P v)) hall v hpv) hex }
    { assume hc; refine ¬¬ₑ _ (λ hne,
        hc (pi_to_!! (λ v, ¬ (P v))
              (λ v hpv, hne (pi_to_??_intro P v hpv)))) }
end;

// NRM1 bridge: ((♢_:Tuple n, P) ⇒ Q) = (P ⇒ Q) when P is x-free.
opaque symbol nrm1_eq [n] [P Q : Prop]
  : π (((`♢ _ : Tuple n, P) ⇒ Q) = (P ⇒ Q)) ≔
begin
  assume n P Q;
  have h1 : π ((`♢ _ : Tuple n, P) = P)
    { refine eq_trans (♢_eq_!! (λ _ : Tuple n, P)) (!!_const [n] P) };
  rewrite h1; reflexivity
end;

// NRM14 bridge: ((♢v·¬P v) ⇒ R) = ((♡v·¬(⊤ ∧ P v)) ⇒ R).  ⊤ ∧ X ⟺ X, so the
// ⊤-padded ♡ body matches the bare ♢ body; ♢/♡ both reduce to !!, so !!_cong
// lifts the per-v equality.  Used by NRM14_1 (the chain-form NRM14).
opaque symbol nrm14_eq [n] [P : Tuple n → Prop] [R : Prop]
  : π (((`♢ v, ¬ (P v)) ⇒ R) = ((`♡ v, ¬ ⋀_snoc ⊤ (P v)) ⇒ R)) ≔
begin
  assume n P R;
  have hbody : Π v, π ((¬ (P v)) = (¬ ⋀_snoc ⊤ (P v)))
    { assume v;
      refine propExt _ _
        (λ hnp hcon, hnp (⋀₂_snd hcon))
        (λ hncon hp, hncon (⋀₂_intro ⊤ᵢ hp)) };
  have hpred : π ((`♢ v, ¬ (P v)) = (`♡ v, ¬ ⋀_snoc ⊤ (P v)))
    { refine eq_trans (♢_eq_!! (λ v, ¬ (P v)))
        (eq_trans (!!_cong hbody)
                  (eq_sym (♡_eq_!! (λ v, ¬ ⋀_snoc ⊤ (P v))))) };
  rewrite hpred; reflexivity
end;

// NRM13 bridge: ((♢v·(P v ⇒ Q v)) ⇒ R) = ((♡v·¬(P v ∧ ¬Q v)) ⇒ R).  The body
// equivalence (P⇒Q) ⟺ ¬(P ∧ ¬Q) is classical (needs `em` on Q v); ♢/♡ both
// reduce to !!, so !!_cong lifts it.  Used by NRM13_1 (the chain-form NRM13).
opaque symbol nrm13_eq [n] [P Q : Tuple n → Prop] [R : Prop]
  : π (((`♢ v, P v ⇒ Q v) ⇒ R) = ((`♡ v, ¬ ⋀_snoc (P v) (¬ Q v)) ⇒ R)) ≔
begin
  assume n P Q R;
  have hbody : Π v, π ((P v ⇒ Q v) = (¬ ⋀_snoc (P v) (¬ Q v)))
    { assume v;
      refine propExt _ _
        (λ hpq hcon, (⋀₂_snd hcon) (hpq (⋀₂_hd hcon)))
        (λ hncon hp, ∨ₑ (em (Q v)) (λ hq, hq)
                       (λ hnq, ⊥ₑ (hncon (⋀₂_intro hp hnq)))) };
  have hpred : π ((`♢ v, P v ⇒ Q v) = (`♡ v, ¬ ⋀_snoc (P v) (¬ Q v)))
    { refine eq_trans (♢_eq_!! (λ v, P v ⇒ Q v))
        (eq_trans (!!_cong hbody)
                  (eq_sym (♡_eq_!! (λ v, ¬ ⋀_snoc (P v) (¬ Q v))))) };
  rewrite hpred; reflexivity
end;

// NRM12 bridge: ((♢v·(P v ⇒ ¬Q v)) ⇒ R) = ((♡v·¬(P v ∧ Q v)) ⇒ R).  The body
// equivalence (P ⇒ ¬Q) ⟺ ¬(P ∧ Q) is constructive.  Used by NRM12_1.
opaque symbol nrm12_eq [n] [P Q : Tuple n → Prop] [R : Prop]
  : π (((`♢ v, P v ⇒ ¬ (Q v)) ⇒ R) = ((`♡ v, ¬ ⋀_snoc (P v) (Q v)) ⇒ R)) ≔
begin
  assume n P Q R;
  have hbody : Π v, π ((P v ⇒ ¬ (Q v)) = (¬ ⋀_snoc (P v) (Q v)))
    { assume v;
      refine propExt _ _
        (λ hpnq hcon, (hpnq (⋀₂_hd hcon)) (⋀₂_snd hcon))
        (λ hncon hp hq, hncon (⋀₂_intro hp hq)) };
  have hpred : π ((`♢ v, P v ⇒ ¬ (Q v)) = (`♡ v, ¬ ⋀_snoc (P v) (Q v)))
    { refine eq_trans (♢_eq_!! (λ v, P v ⇒ ¬ (Q v)))
        (eq_trans (!!_cong hbody)
                  (eq_sym (♡_eq_!! (λ v, ¬ ⋀_snoc (P v) (Q v))))) };
  rewrite hpred; reflexivity
end;

// NRM5 bridge: ((♢v·(P v ⇒ Q v ⇒ R v)) ⇒ S) = ((♢v·(⋀_snoc (P v) (Q v) ⇒ R v)) ⇒ S).
// Body equivalence is curry/uncurry — (P ⇒ Q ⇒ R) ⟺ ((P ∧ Q) ⇒ R) — constructive.
// Both sides ♢.  Used by NRM5_1.
opaque symbol nrm5_eq [n] [P Q R : Tuple n → Prop] [S : Prop]
  : π (((`♢ v, P v ⇒ Q v ⇒ R v) ⇒ S)
       = ((`♢ v, ⋀_snoc (P v) (Q v) ⇒ R v) ⇒ S)) ≔
begin
  assume n P Q R S;
  have hbody : Π v, π ((P v ⇒ Q v ⇒ R v) = (⋀_snoc (P v) (Q v) ⇒ R v))
    { assume v;
      refine propExt _ _
        (λ hpqr hpq, hpqr (⋀₂_hd hpq) (⋀₂_snd hpq))
        (λ hcr hp hq, hcr (⋀₂_intro hp hq)) };
  have hpred : π ((`♢ v, P v ⇒ Q v ⇒ R v) = (`♢ v, ⋀_snoc (P v) (Q v) ⇒ R v))
    { refine eq_trans (♢_eq_!! (λ v, P v ⇒ Q v ⇒ R v))
        (eq_trans (!!_cong hbody)
                  (eq_sym (♢_eq_!! (λ v, ⋀_snoc (P v) (Q v) ⇒ R v)))) };
  rewrite hpred; reflexivity
end;

// NRM10 bridge: ((♢v·(⋀(Ps v ∷ Q v) ⇒ ⊥)) ⇒ R) = ((♡v·¬⋀(Ps v ∷ Q v)) ⇒ R).
// The body `(C ⇒ ⊥) = ¬C` is reflexivity (¬ ≔ ⇒⊥); ♢/♡ both reduce to !!.  NRM10_1.
opaque symbol nrm10_eq [n] [Ps : Tuple n → 𝕃* o] [Q : Tuple n → Prop] [R : Prop]
  : π (((`♢ v, ⋀ (Ps v ∷ Q v) ⇒ ⊥) ⇒ R)
       = ((`♡ v, ¬ ⋀ (Ps v ∷ Q v)) ⇒ R)) ≔
begin
  assume n Ps Q R;
  have hpred : π ((`♢ v, ⋀ (Ps v ∷ Q v) ⇒ ⊥) = (`♡ v, ¬ ⋀ (Ps v ∷ Q v)))
    { refine eq_trans (♢_eq_!! (λ v, ⋀ (Ps v ∷ Q v) ⇒ ⊥))
        (eq_sym (♡_eq_!! (λ v, ¬ ⋀ (Ps v ∷ Q v)))) };
  rewrite hpred; reflexivity
end;

// NRM24 bridge: ((♡v·¬(P v)) ⇒ Q) = ((♡v·¬⋀(∎ ∷ ⊤ ∷ P v)) ⇒ Q).  Body: ¬P ⟺
// ¬(⊤ ∧ P) (drop the leading ⊤).  Both sides ♡.  Used by NRM24_1.
opaque symbol nrm24_eq [n] [P : Tuple n → Prop] [Q : Prop]
  : π (((`♡ v, ¬ (P v)) ⇒ Q)
       = ((`♡ v, ¬ ⋀ (∎ ∷ ⊤ ∷ P v)) ⇒ Q)) ≔
begin
  assume n P Q;
  have hbody : Π v, π ((¬ (P v)) = (¬ ⋀ (∎ ∷ ⊤ ∷ P v)))
    { assume v;
      refine propExt _ _
        (λ hnp hcon, hnp (⋀₂_snd hcon))
        (λ hncon hp, hncon (⋀₂_intro ⊤ᵢ hp)) };
  have hpred : π ((`♡ v, ¬ (P v)) = (`♡ v, ¬ ⋀ (∎ ∷ ⊤ ∷ P v)))
    { refine eq_trans (♡_eq_!! (λ v, ¬ (P v)))
        (eq_trans (!!_cong hbody)
                  (eq_sym (♡_eq_!! (λ v, ¬ ⋀ (∎ ∷ ⊤ ∷ P v))))) };
  rewrite hpred; reflexivity
end;

// NRM15 bridge: ((♢v·P v) ⇒ R) = ((♡v·¬(⊤ ∧ ¬P v)) ⇒ R).  The body
// equivalence P ⟺ ¬(⊤ ∧ ¬P) is classical (¬¬ₑ).  Used by NRM15_1.
opaque symbol nrm15_eq [n] [P : Tuple n → Prop] [R : Prop]
  : π (((`♢ v, P v) ⇒ R) = ((`♡ v, ¬ ⋀_snoc ⊤ (¬ (P v))) ⇒ R)) ≔
begin
  assume n P R;
  have hbody : Π v, π ((P v) = (¬ ⋀_snoc ⊤ (¬ (P v))))
    { assume v;
      refine propExt _ _
        (λ hp hcon, (⋀₂_snd hcon) hp)
        (λ hncon, ¬¬ₑ (P v) (λ hnp, hncon (⋀₂_intro ⊤ᵢ hnp))) };
  have hpred : π ((`♢ v, P v) = (`♡ v, ¬ ⋀_snoc ⊤ (¬ (P v))))
    { refine eq_trans (♢_eq_!! (λ v, P v))
        (eq_trans (!!_cong hbody)
                  (eq_sym (♡_eq_!! (λ v, ¬ ⋀_snoc ⊤ (¬ (P v)))))) };
  rewrite hpred; reflexivity
end;

// NRM23 bridge: ((♡v:Tuple1·¬(⊤ ∧ (E = prj 0 v))) ⇒ Q) = (¬⊤ ⇒ Q).  The ♡ body
// is ¬(E = prj 0 v); over Tuple 1 the witness v = unit⨾E makes it absurd, so the
// quantified head collapses to ¬⊤.  Used by NRM23_1 (the chain-form NRM23).
opaque symbol nrm23_eq [Q : Prop] (E : τ ι)
  : π (((`♡ v : Tuple 1, ¬ ⋀ (∎ ∷ ⊤ ∷ (E = prj 0 v))) ⇒ Q) = (¬ ⊤ ⇒ Q)) ≔
begin
  assume Q E;
  have hpred : π ((`♡ v : Tuple 1, ¬ ⋀ (∎ ∷ ⊤ ∷ (E = prj 0 v))) = ¬ ⊤)
    { refine propExt _ _
        (λ h♡ ht, ♡_to_pi (λ v : Tuple 1, ¬ ⋀ (∎ ∷ ⊤ ∷ (E = prj 0 v)))
                          h♡ (unit ⨾ E) (⋀₂_intro ht (eq_refl E)))
        (λ hn⊤, ⊥ₑ (hn⊤ ⊤ᵢ)) };
  rewrite hpred; reflexivity
end;

// NRM22 bridge, general form: the ♡-body's *tail* equality pins the
// binder (`¬(⋀(ps v) ∧ (prj 0 v = E))` ⟺ the body refuted at v := E), so
// the quantified head collapses to `¬ ⋀ (ps (unit ⨾ E))`.  The body is a
// *list* `ps v ∷ (prj 0 v = E)` so the cons pattern unifies with any
// conjunct count; the ⊤-headed shape is the instance ps := λ _, (∎ ∷ ⊤).
// The ⇐ direction needs the per-constructor case split, so it goes
// through a helper with a rewrite rule on `(unit ⨾ a)` (the
// nested_to_compound pattern).
symbol nrm22_pin (ps : Tuple 1 → 𝕃* o) (E : τ ι)
  (hnp : π (¬ ⋀ (ps (unit ⨾ E))))
  : Π v : Tuple 1, π (¬ ⋀ (ps v ∷ (prj 0 v = E)));
rule nrm22_pin $ps $E $hnp (unit ⨾ $a) ↪
  λ hcon, $hnp (ind_eq (eq_sym (⋀_last hcon))
                       (λ z, ⋀ ($ps (unit ⨾ z)))
                       (⋀_init hcon));

opaque symbol nrm22_eq [Q : Prop] [ps : Tuple 1 → 𝕃* o] (E : τ ι)
  : π (((`♡ v : Tuple 1, ¬ ⋀ (ps v ∷ (prj 0 v = E))) ⇒ Q)
       = ((¬ ⋀ (ps (unit ⨾ E))) ⇒ Q)) ≔
begin
  assume Q ps E;
  have hpred : π ((`♡ v : Tuple 1, ¬ ⋀ (ps v ∷ (prj 0 v = E)))
                  = (¬ ⋀ (ps (unit ⨾ E))))
    { refine propExt _ _
        (λ h♡ hps, ♡_to_pi (λ v : Tuple 1, ¬ ⋀ (ps v ∷ (prj 0 v = E)))
                           h♡ (unit ⨾ E) (⋀_intro hps (eq_refl E)))
        (λ hnp, pi_to_♡ (λ v : Tuple 1, ¬ ⋀ (ps v ∷ (prj 0 v = E)))
                        (nrm22_pin ps E hnp)) };
  rewrite hpred; reflexivity
end;

// NRM4 bridge: ((♢v·(P v ⇒ Q ⇒ R v)) ⇒ S) = ((Q ⇒ (♢v·(P v ⇒ R v))) ⇒ S), Q is
// v-free.  Not a per-v body congruence: Q pulls *out* of the ♢ (∀v·(Q⇒X v) ⟺
// Q⇒∀v·X v), composed with antecedent-swap (P⇒Q⇒R ⟺ Q⇒P⇒R).  Used by NRM4_1.
opaque symbol nrm4_eq [n] [P R : Tuple n → Prop] [Q S : Prop]
  : π (((`♢ v, P v ⇒ Q ⇒ R v) ⇒ S) = ((Q ⇒ (`♢ v, P v ⇒ R v)) ⇒ S)) ≔
begin
  assume n P R Q S;
  have hpred : π ((`♢ v, P v ⇒ Q ⇒ R v) = (Q ⇒ (`♢ v, P v ⇒ R v)))
    { refine propExt _ _
        (λ hall hq, pi_to_♢ (λ v, P v ⇒ R v)
           (λ v hpv, ♢_to_pi (λ v', P v' ⇒ Q ⇒ R v') hall v hpv hq))
        (λ himp, pi_to_♢ (λ v, P v ⇒ Q ⇒ R v)
           (λ v hpv hq, ♢_to_pi (λ v', P v' ⇒ R v') (himp hq) v hpv)) };
  rewrite hpred; reflexivity
end;

// NRM7 bridge: ((♢v·⋀(Qs v ∷ P v)) ⇒ S) = ((♢v·⋀(Qs v)) ⇒ ((♢v·P v) ⇒ S)).
// ∀ distributes over ∧ and ⋀(Qs∷P) splits init/last, so the single ♢ premise
// curries into two; whole-implication propExt.  Used by NRM7_1.
opaque symbol nrm7_eq [n] [Qs : Tuple n → 𝕃* o] [P : Tuple n → Prop] [S : Prop]
  : π (((`♢ v, ⋀ (Qs v ∷ P v)) ⇒ S)
       = ((`♢ v, ⋀ (Qs v)) ⇒ ((`♢ v, P v) ⇒ S))) ≔
begin
  assume n Qs P S;
  refine propExt _ _
    (λ hres hqs hp, hres (pi_to_♢ (λ v, ⋀ (Qs v ∷ P v))
       (λ v, ⋀_intro (♢_to_pi (λ v', ⋀ (Qs v')) hqs v) (♢_to_pi P hp v))))
    (λ hcur hc, hcur
       (pi_to_♢ (λ v, ⋀ (Qs v))
          (λ v, ⋀_init (♢_to_pi (λ v', ⋀ (Qs v' ∷ P v')) hc v)))
       (pi_to_♢ P
          (λ v, ⋀_last (♢_to_pi (λ v', ⋀ (Qs v' ∷ P v')) hc v))))
end;

// NRM11 bridge: ((♢v·(P v ⇒ ⊥)) ⇒ R) = ((♡v·¬⋀_snoc ⊤ (P v)) ⇒ R).  Body
// (P⇒⊥) ⟺ ¬(⊤∧P) (¬ ≔ ⇒⊥, drop the ⊤); ♢/♡ both reduce to !!.  Used by NRM11_1.
opaque symbol nrm11_eq [n] [P : Tuple n → Prop] [R : Prop]
  : π (((`♢ v, P v ⇒ ⊥) ⇒ R) = ((`♡ v, ¬ ⋀_snoc ⊤ (P v)) ⇒ R)) ≔
begin
  assume n P R;
  have hbody : Π v, π ((P v ⇒ ⊥) = (¬ ⋀_snoc ⊤ (P v)))
    { assume v;
      refine propExt _ _
        (λ hpb hcon, hpb (⋀₂_snd hcon))
        (λ hncon hp, hncon (⋀₂_intro ⊤ᵢ hp)) };
  have hpred : π ((`♢ v, P v ⇒ ⊥) = (`♡ v, ¬ ⋀_snoc ⊤ (P v)))
    { refine eq_trans (♢_eq_!! (λ v, P v ⇒ ⊥))
        (eq_trans (!!_cong hbody)
                  (eq_sym (♡_eq_!! (λ v, ¬ ⋀_snoc ⊤ (P v))))) };
  rewrite hpred; reflexivity
end;

// NRM25 bridge: ((♡_:Tuple n, P) ⇒ Q) = (P ⇒ Q), P x-free (the ♡ mirror of
// nrm1_eq).  Used by NRM25_1.
opaque symbol nrm25_eq [n] [P Q : Prop]
  : π (((`♡ _ : Tuple n, P) ⇒ Q) = (P ⇒ Q)) ≔
begin
  assume n P Q;
  have h1 : π ((`♡ _ : Tuple n, P) = P)
    { refine eq_trans (♡_eq_!! (λ _ : Tuple n, P)) (!!_const [n] P) };
  rewrite h1; reflexivity
end;

// NRM8 bridge: ((♢x·!!y·Q x y) ⇒ S) = ((♢v:n++m·Q(take v)(drop v)) ⇒ S).  The
// compound↔nested split for the general inner arity m (`!!_split_eq_m`,
// lemmas/Tuple.lp), sandwiched between ♢↔!! on each binder.  Used by NRM8_1.
opaque symbol nrm8_eq [n m] [Q : Tuple n → Tuple m → Prop] [S : Prop]
  : π (((`♢ x : Tuple n, `!! y : Tuple m, Q x y) ⇒ S)
       = ((`♢ v : Tuple (n ++ m), Q (take [n] [m] v) (drop [n] [m] v)) ⇒ S)) ≔
begin
  assume n m Q S;
  have hpred : π ((`♢ x : Tuple n, `!! y : Tuple m, Q x y)
                  = (`♢ v : Tuple (n ++ m), Q (take [n] [m] v) (drop [n] [m] v)))
    { refine eq_trans (♢_eq_!! (λ x : Tuple n, `!! y : Tuple m, Q x y))
        (eq_trans (eq_sym (!!_split_eq_m Q))
          (eq_sym (♢_eq_!!
            (λ v : Tuple (n ++ m), Q (take [n] [m] v) (drop [n] [m] v))))) };
  rewrite hpred; reflexivity
end;

// NRM9 bridge: ((♢x·(P x ⇒ !!y·Q x y)) ⇒ S) = ((♢v·(P(take v) ⇒ Q(take v)(drop v))) ⇒ S).
// Pull the inner `!!y` out of the implication (y ∉ P), then NRM8's split.  NRM9_1.
opaque symbol nrm9_eq [n m] [P : Tuple n → Prop] [Q : Tuple n → Tuple m → Prop] [S : Prop]
  : π (((`♢ x : Tuple n, P x ⇒ (`!! y : Tuple m, Q x y)) ⇒ S)
       = ((`♢ v : Tuple (n ++ m),
            P (take [n] [m] v) ⇒ Q (take [n] [m] v) (drop [n] [m] v)) ⇒ S)) ≔
begin
  assume n m P Q S;
  have hbody : Π x, π ((P x ⇒ (`!! y : Tuple m, Q x y))
                       = (`!! y : Tuple m, P x ⇒ Q x y))
    { assume x;
      refine propExt _ _
        (λ h, pi_to_!! (λ y, P x ⇒ Q x y) (λ y hp, !!_to_pi (Q x) (h hp) y))
        (λ h hp, pi_to_!! (Q x) (λ y, !!_to_pi (λ y', P x ⇒ Q x y') h y hp)) };
  have hpred : π ((`♢ x : Tuple n, P x ⇒ (`!! y : Tuple m, Q x y))
                  = (`♢ v : Tuple (n ++ m),
                       P (take [n] [m] v) ⇒ Q (take [n] [m] v) (drop [n] [m] v)))
    { refine eq_trans (♢_eq_!! (λ x : Tuple n, P x ⇒ (`!! y : Tuple m, Q x y)))
        (eq_trans (!!_cong hbody)
          (eq_trans (eq_sym (!!_split_eq_m (λ x y, P x ⇒ Q x y)))
            (eq_sym (♢_eq_!!
              (λ v : Tuple (n ++ m),
                 P (take [n] [m] v) ⇒ Q (take [n] [m] v) (drop [n] [m] v)))))) };
  rewrite hpred; reflexivity
end;

// NRM6 bridge: ((♢v·(R v ⇒ ⋀(Qs v ∷ P v))) ⇒ S)
//            = ((♢v·(R v ⇒ ⋀(Qs v))) ⇒ ((♢v·(R v ⇒ P v)) ⇒ S)).
// Like NRM7 with the `R ⇒` guard: ∀ distributes over the ⋀ init/last split, so
// the single premise curries into two.  Whole-implication propExt.  Used by NRM6_1.
opaque symbol nrm6_eq [n] [Qs : Tuple n → 𝕃* o] [P R : Tuple n → Prop] [S : Prop]
  : π (((`♢ v, R v ⇒ ⋀ (Qs v ∷ P v)) ⇒ S)
       = ((`♢ v, R v ⇒ ⋀ (Qs v)) ⇒ ((`♢ v, R v ⇒ P v) ⇒ S))) ≔
begin
  assume n Qs P R S;
  refine propExt _ _
    (λ hres hqs hp, hres (pi_to_♢ (λ v, R v ⇒ ⋀ (Qs v ∷ P v))
       (λ v hr, ⋀_intro (♢_to_pi (λ v', R v' ⇒ ⋀ (Qs v')) hqs v hr)
                        (♢_to_pi (λ v', R v' ⇒ P v') hp v hr))))
    (λ hcur hc, hcur
       (pi_to_♢ (λ v, R v ⇒ ⋀ (Qs v))
          (λ v hr, ⋀_init (♢_to_pi (λ v', R v' ⇒ ⋀ (Qs v' ∷ P v')) hc v hr)))
       (pi_to_♢ (λ v, R v ⇒ P v)
          (λ v hr, ⋀_last (♢_to_pi (λ v', R v' ⇒ ⋀ (Qs v' ∷ P v')) hc v hr))))
end;
