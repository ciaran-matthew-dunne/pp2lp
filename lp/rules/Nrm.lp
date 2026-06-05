// Normalisation (§A.12) — tuple-based encoding.
//
// Spec uses `♢` (= goal-side n-ary universal) and `♡` (= hypothesis-
// side n-ary universal). Both reduce propositionally to `!!` via the
// `♢_eq_!!` / `♡_eq_!!` axioms in Quant.lp; bodies use the dedicated
// `pi_to_♢` / `♢_to_pi` (and ♡ analogues) bridges.

require open pp2lp.B pp2lp.Quant pp2lp.rules.Res;

// ---- NRM1-7: Logical transformations under `♢` ----

// NRM1: x not free in P; H ⊢ P ⇒ S → H ⊢ (♢x · P) ⇒ S
opaque symbol NRM1 [n] [P S : Prop]
  : π (P ⇒ S)
  → π ((`♢ _ : Tuple n, P) ⇒ S) ≔
begin
  assume n P S h1 h2;
  refine h1 (♢_to_pi (λ _ : Tuple n, P) h2 (inh_tuple [n]))
end;

// NRM2: x not free in P; H ⊢ (P ⇒ ♢x · Q) ⇒ S → H ⊢ ♢x · (P ⇒ Q) ⇒ S
opaque symbol NRM2 [n] [P : Prop] [Q : Tuple n → Prop] [S : Prop]
  : π ((P ⇒ (`♢ v, Q v)) ⇒ S)
  → π ((`♢ v, P ⇒ Q v) ⇒ S) ≔
begin
  assume n P Q S h1 h2;
  refine h1 (λ p,
    pi_to_♢ Q (λ v, ♢_to_pi (λ v', P ⇒ Q v') h2 v p))
end;

// NRM3: x not free in Q; H ⊢ (Q ⇒ S) ∧ ((∀x · ¬P) ⇒ S) → H ⊢ ♢x · (P ⇒ Q) ⇒ S
opaque symbol NRM3 [n] [P : Tuple n → Prop] [Q S : Prop]
  : π (⋀_snoc (Q ⇒ S) ((`!! v, ¬ (P v)) ⇒ S))
  → π ((`♢ v, P v ⇒ Q) ⇒ S) ≔
begin
  assume n P Q S h1 h2;
  refine ∨ₑ (em (`?? v, P v)) _ _
  { assume hex;
    refine pi_to_??_elim P
      (λ v hpv, (⋀₂_hd h1) (♢_to_pi (λ v', P v' ⇒ Q) h2 v hpv)) hex }
  { assume hnex;
    refine (⋀₂_snd h1) (pi_to_!! (λ v, ¬ (P v))
      (λ v hpv, hnex (pi_to_??_intro P v hpv))) }
end;

// NRM4: x not free in Q; H ⊢ (Q ⇒ ♢x · (P ⇒ R)) ⇒ S → H ⊢ ♢x · (P ⇒ Q ⇒ R) ⇒ S
opaque symbol NRM4 [n] [P R : Tuple n → Prop] [Q S : Prop]
  : π ((Q ⇒ (`♢ v, P v ⇒ R v)) ⇒ S)
  → π ((`♢ v, P v ⇒ Q ⇒ R v) ⇒ S) ≔
begin
  assume n P R Q S h1 h2;
  refine h1 (λ hq,
    pi_to_♢ (λ v, P v ⇒ R v)
      (λ v hpv, ♢_to_pi (λ v', P v' ⇒ Q ⇒ R v') h2 v hpv hq))
end;

// NRM5: H ⊢ ♢x · (P ∧ Q ⇒ R) ⇒ S → H ⊢ ♢x · (P ⇒ Q ⇒ R) ⇒ S
// Uncurry: `⋀_snoc (P v) (Q v)` reduces to `⋀ (∎ ∷ P v ∷ Q v)`, so the
// hypothesis splits with `⋀₂_hd`/`⋀₂_snd` to feed the curried body.
opaque symbol NRM5 [n] [P Q R : Tuple n → Prop] [S : Prop]
  : π ((`♢ v, ⋀_snoc (P v) (Q v) ⇒ R v) ⇒ S)
  → π ((`♢ v, P v ⇒ Q v ⇒ R v) ⇒ S) ≔
begin
  assume n P Q R S h1 h2;
  refine h1 (pi_to_♢ (λ v, ⋀_snoc (P v) (Q v) ⇒ R v)
    (λ v hpq, ♢_to_pi (λ v', P v' ⇒ Q v' ⇒ R v') h2 v
                (⋀₂_hd hpq) (⋀₂_snd hpq)))
end;

// NRM6: H ⊢ ♢x · (R ⇒ P) ⇒ (♢x · (R ⇒ Q) ⇒ S) → H ⊢ ♢x · (R ⇒ P ∧ Q) ⇒ S
// Generalised over a snoc list: the consequent `⋀ (qs v ∷ P v)` splits into
// init `⋀ (qs v)` and last `P v`.  init-first lets the emitter chain
// `refine NRM6 _;` for n-conjunct goals, since `⋀ (qs v)` is itself a
// `⋀ (qs' v ∷ P' v)` when |qs v| ≥ 2.
opaque symbol NRM6 [n] [Qs : Tuple n → 𝕃* o] [P R : Tuple n → Prop] [S : Prop]
  : π ((`♢ v, R v ⇒ ⋀ (Qs v)) ⇒ ((`♢ v, R v ⇒ P v) ⇒ S))
  → π ((`♢ v, R v ⇒ ⋀ (Qs v ∷ P v)) ⇒ S) ≔
begin
  assume n qs P R S h1 h2;
  refine h1
    (pi_to_♢ (λ v, R v ⇒ ⋀ (qs v))
      (λ v hr, ⋀_init (♢_to_pi (λ v', R v' ⇒ ⋀ (qs v' ∷ P v')) h2 v hr)))
    (pi_to_♢ (λ v, R v ⇒ P v)
      (λ v hr, ⋀_last (♢_to_pi (λ v', R v' ⇒ ⋀ (qs v' ∷ P v')) h2 v hr)))
end;

// NRM7: H ⊢ (♢x · P) ⇒ ((♢x · Q) ⇒ S) → H ⊢ ♢x · (P ∧ Q) ⇒ S
// Generalised: same shape as NRM6 but without the R ⇒ antecedent.
opaque symbol NRM7 [n] [Qs : Tuple n → 𝕃* o] [P : Tuple n → Prop] [S : Prop]
  : π ((`♢ v, ⋀ (Qs v))
        ⇒ ((`♢ v, P v) ⇒ S))
  → π ((`♢ v : Tuple n, ⋀ (Qs v ∷ P v)) ⇒ S) ≔
begin
  assume n qs P S h1 h2;
  refine h1
    (pi_to_♢ (λ v, ⋀ (qs v))
      (λ v, ⋀_init (♢_to_pi (λ v', ⋀ (qs v' ∷ P v')) h2 v)))
    (pi_to_♢ (λ v, P v)
      (λ v, ⋀_last (♢_to_pi (λ v', ⋀ (qs v' ∷ P v')) h2 v)))
end;

// ---- NRM8-9: compound↔mixed binders (split with `take`/`drop`) ----
//
// NRM8: spec is `(♢(x,y) · Q) ⇒ S` ← `(♢x · ∀y · Q) ⇒ S`.
// Encoded with the n,m-indexed split helpers from Quant.lp:
//   the conclusion's `Q x y` (clean HO pattern) gets unified back
//   from the premise's `Q (take v) (drop v)` after Lambdapi infers Q.
opaque symbol NRM8 [n m] [Q : Tuple n → Tuple m → Prop] [S : Prop]
  : π ((`♢ v : Tuple (n ++ m), Q (take [n] [m] v) (drop [n] [m] v)) ⇒ S)
  → π ((`♢ x : Tuple n, `!! y : Tuple m, Q x y) ⇒ S) ≔
begin
  assume n m Q S h hnested;
  // hnested : π (`♢ x : Tuple n, `!! y : Tuple m, Q x y)
  // Need:    π (`♢ v : Tuple (n ++ m), Q (take v) (drop v))
  // Witness: λ v, !!_to_pi (Q x) (♢_to_pi (λ x, `!! y, Q x y) hnested x') y'
  //          where x' = take v, y' = drop v.
  refine h (pi_to_♢ (λ v : Tuple (n ++ m),
                       Q (take [n] [m] v) (drop [n] [m] v))
    (λ v : Tuple (n ++ m),
       !!_to_pi (λ y, Q (take [n] [m] v) y)
                (♢_to_pi (λ x, `!! y : Tuple m, Q x y)
                         hnested
                         (take [n] [m] v))
                (drop [n] [m] v)))
end;

// NRM9: spec is `(♢(x,y) · (P ⇒ Q)) ⇒ S` ← `(♢x · (P ⇒ ∀y · Q)) ⇒ S`,
// with y not free in P. Same split: premise body is `P (take v) ⇒ Q (take v) (drop v)`.
opaque symbol NRM9 [n m]
  [P : Tuple n → Prop]
  [Q : Tuple n → Tuple m → Prop]
  [S : Prop]
  : π ((`♢ v : Tuple (n ++ m),
         P (take [n] [m] v) ⇒ Q (take [n] [m] v) (drop [n] [m] v)) ⇒ S)
  → π ((`♢ x : Tuple n, P x ⇒ (`!! y : Tuple m, Q x y)) ⇒ S) ≔
begin
  assume n m P Q S h hnested;
  refine h (pi_to_♢
    (λ v, P (take [n] [m] v) ⇒ Q (take [n] [m] v) (drop [n] [m] v))
    (λ v hp,
       !!_to_pi (λ y, Q (take [n] [m] v) y)
                (♢_to_pi (λ x, P x ⇒ (`!! y : Tuple m, Q x y))
                         hnested
                         (take [n] [m] v)
                         hp)
                (drop [n] [m] v)))
end;

// ---- NRM10-15: Implication / negation under `♢` and `♡` ----

// NRM10: H ⊢ ♡x · ¬(P ∧ Q) ⇒ R → H ⊢ ♢x · (P ∧ Q ⇒ ⊥) ⇒ R
opaque symbol NRM10 [n] [Ps : Tuple n → 𝕃* o] [Q : Tuple n → Prop] [R : Prop]
  : π ((`♡ v, ¬ ⋀ (Ps v ∷ Q v)) ⇒ R)
  → π ((`♢ v, ⋀ (Ps v ∷ Q v) ⇒ ⊥) ⇒ R) ≔
begin
  assume n Ps Q R h1 h2;
  refine h1 (pi_to_♡ (λ v, ¬ ⋀ (Ps v ∷ Q v))
    (λ v hpq, ♢_to_pi (λ v', ⋀ (Ps v' ∷ Q v') ⇒ ⊥) h2 v hpq))
end;

// NRM11: H ⊢ ♡x · ¬(⊤ ∧ P) ⇒ R → H ⊢ ♢x · (P ⇒ ⊥) ⇒ R
opaque symbol NRM11 [n] [P : Tuple n → Prop] [R : Prop]
  : π ((`♡ v, ¬ (⋀_snoc ⊤ (P v))) ⇒ R)
  → π ((`♢ v, P v ⇒ ⊥) ⇒ R) ≔
begin
  assume n P R h1 h2;
  refine h1 (pi_to_♡ (λ v, ¬ ⋀ (∎ ∷ ⊤ ∷ P v))
    (λ v htpv, ♢_to_pi (λ v', P v' ⇒ ⊥) h2 v (⋀₂_snd htpv)))
end;

// NRM12: H ⊢ ♡x · ¬(P ∧ Q) ⇒ R → H ⊢ ♢x · (P ⇒ ¬Q) ⇒ R
opaque symbol NRM12 [n] [P Q : Tuple n → Prop] [R : Prop]
  : π ((`♡ v, ¬ ⋀_snoc (P v) (Q v)) ⇒ R)
  → π ((`♢ v, P v ⇒ ¬ (Q v)) ⇒ R) ≔
begin
  assume n P Q R h1 h2;
  refine h1 (pi_to_♡ (λ v, ¬ ⋀ (∎ ∷ P v ∷ Q v))
    (λ v hpq, ♢_to_pi (λ v', P v' ⇒ ¬ (Q v')) h2 v
                (⋀₂_hd hpq) (⋀₂_snd hpq)))
end;

// NRM13: H ⊢ ♡x · ¬(P ∧ ¬Q) ⇒ R → H ⊢ ♢x · (P ⇒ Q) ⇒ R
opaque symbol NRM13 [n] [P Q : Tuple n → Prop] [R : Prop]
  : π ((`♡ v, ¬ ⋀_snoc (P v) (¬ Q v)) ⇒ R)
  → π ((`♢ v, P v ⇒ Q v) ⇒ R) ≔
begin
  assume n P Q R h1 h2;
  refine h1 (pi_to_♡ (λ v, ¬ ⋀ (∎ ∷ P v ∷ ¬ (Q v)))
    (λ v hc, (⋀₂_snd hc) (♢_to_pi (λ v', P v' ⇒ Q v') h2 v (⋀₂_hd hc))))
end;

// NRM14: H ⊢ ♡x · ¬(⊤ ∧ P) ⇒ R → H ⊢ (♢x · ¬P) ⇒ R
opaque symbol NRM14 [n] [P : Tuple n → Prop] [R : Prop]
  : π ((`♡ v, ¬ ⋀_snoc ⊤ (P v)) ⇒ R)
  → π ((`♢ v, ¬ (P v)) ⇒ R) ≔
begin
  assume n P R h1 h2;
  refine h1 (pi_to_♡ (λ v, ¬ ⋀ (∎ ∷ ⊤ ∷ P v))
    (λ v htpv, ♢_to_pi (λ v', ¬ (P v')) h2 v (⋀₂_snd htpv)))
end;

// NRM15: H ⊢ ♡x · ¬(⊤ ∧ ¬P) ⇒ R → H ⊢ (♢x · P) ⇒ R
opaque symbol NRM15 [n] [P : Tuple n → Prop] [R : Prop]
  : π ((`♡ v, ¬ ⋀_snoc ⊤ (¬ P v)) ⇒ R)
  → π ((`♢ v, P v) ⇒ R) ≔
begin
  assume n P R h1 h2;
  refine h1 (pi_to_♡ (λ v, ¬ ⋀ (∎ ∷ ⊤ ∷ ¬ (P v)))
    (λ v htnpv, (⋀₂_snd htnpv) (♢_to_pi P h2 v)))
end;

// ---- NRM16-19: Universal-instantiation patterns ----

// NRM16: ∀x.P in H; Q → H ⊢ (♡x · P) ⇒ Q
opaque symbol NRM16 [n] [P : Tuple n → Prop] [Q : Prop]
  : π (`!! v, P v)
  → π Q
  → π ((`♡ v, P v) ⇒ Q) ≔
begin
  assume n P Q hp hq ht; refine hq
end;

// NRM17: NRM16 with extra spec-level equality side-conditions.
// At the LP level the proof obligation collapses to NRM16's shape.
opaque symbol NRM17 [n] [P : Tuple n → Prop] [Q : Prop]
  : π (`!! v, P v)
  → π Q
  → π ((`♡ v, P v) ⇒ Q) ≔
begin
  assume n P Q hp hq ht; refine hq
end;

// NRM18: ∀x · ¬(⊤ ∧ ¬P) in H; ∃E. [x:=E]P = R → H ⊢ ♡y · ¬(⊤ ∧ R) ⇒ Q
opaque symbol NRM18 [n] [P : Tuple n → Prop] [R Q : Prop] (v : Tuple n)
  : π (`!! u, ¬ ⋀_snoc ⊤ (¬ P u))
  → π (P v = R)
  → π ((`♡ _ : Tuple n, ¬ ⋀_snoc ⊤ R) ⇒ Q) ≔
begin
  assume n P R Q v hp heq h;
  // Derive π (P v) classically.
  have hpv : π (P v)
    { refine ¬¬ₑ (P v) _;
      assume hnpv;
      refine !!_to_pi (λ u, ¬ ⋀ (∎ ∷ ⊤ ∷ ¬ (P u))) hp v (⋀₂_intro ⊤ᵢ hnpv) };
  // Transport along heq.
  have hr : π R { rewrite left heq; refine hpv };
  refine ⊥ₑ (♡_to_pi (λ _ : Tuple n, ¬ ⋀ (∎ ∷ ⊤ ∷ R)) h (inh_tuple [n])
              (⋀₂_intro ⊤ᵢ hr))
end;

// NRM19: P in H; ∃E. [x:=E]R = P → H ⊢ ♡x · ¬(⊤ ∧ R) ⇒ Q
opaque symbol NRM19 [n] [Q : Prop] [R : Tuple n → Prop] (v : Tuple n)
  : π (R v)
  → π ((`♡ u, ¬ ⋀_snoc ⊤ (R u)) ⇒ Q) ≔
begin
  assume n Q R v hr hf;
  refine ⊥ₑ (♡_to_pi (λ u, ¬ ⋀ (∎ ∷ ⊤ ∷ R u)) hf v (⋀₂_intro ⊤ᵢ hr))
end;

// ---- NRM20-23: Substitution ----

// NRM20: x not free in E; H ⊢ ♡y · ¬[x:=E]P ⇒ Q
//        → H ⊢ ♡(x,y) · ¬(x = E ∧ P) ⇒ Q
//
//   ∀ (x2,..,xn), ¬ (P2(E,..,xn) ∧ .. ∧ Pn(E,...,xn))
//   ----------------------------------------------------------
//   ∀ (x1,..,xn), ¬ ((x1 = E) ∧ P2(x1..xn) ∧ .. ∧ Pn(x1...xn))
//
// `ps v` is the *full* conjunct list.  Its head `popl (ps v)` is the leading
// equality `x1 = E` (≡ `prj 0 v = E`, pinned by the first premise); its tail
// `dropl (ps v)` is the body `P2 ∧ .. ∧ Pn`.  Instantiating the goal's
// universal at `v' ⨾ E` performs the substitution x1 := E: the head becomes
// `E = E` (true by `eq_refl`) and the tail matches the hypothesis's body, so
// `⋀_pop_intro` rebuilds `⋀ (ps (v' ⨾ E))` to discharge the negation.
opaque symbol NRM20 [n] [ps : Tuple (+1 n) → 𝕃* o] [Q : Prop] (E : τ ι)
  : (Π v', π (popl (ps v') = (prj 0 v' = E)))
  → π ((`♡ v' : Tuple n, ¬ ⋀ dropl (ps (v' ⨾ E))) ⇒ Q)
  → π ((`♡ v : Tuple (+1 n), ¬ ⋀ (ps v)) ⇒ Q) ≔
begin
  assume n ps Q E heq hsmall hbig;
  refine hsmall (pi_to_♡ (λ v' : Tuple n, ¬ ⋀ dropl (ps (v' ⨾ E)))
    (λ v' hp,
      ♡_to_pi (λ v, ¬ ⋀ (ps v)) hbig (v' ⨾ E)
        (⋀_pop_intro (ps (v' ⨾ E))
          (=⇒ (eq_sym (heq (v' ⨾ E))) (eq_refl E))
          hp)))
end;

// NRM21 / NRM23 — reversed-equality (`E = x`) duals of NRM20 / NRM22.
//
// UNVERIFIED: no replay in the corpus exercises these, so their signatures
// below are spec-derived and have NOT been checked against PP's actual output.
// NRM20 and NRM22 both needed rewriting once a real replay showed the spec was
// wrong (NRM20's head-equality `ps` list; NRM22's literal-⊤ head) — expect the
// same here.  Before relying on NRM21/23, obtain a triggering trace and re-derive
// the shape from it; the emitter still emits a bare `refine NRM2{1,3} _` (no E),
// which will fail loudly rather than silently mis-prove.
opaque symbol NRM21 [n] [ps : Tuple (+1 n) → 𝕃* o] [Q : Prop] (E : τ ι)
  (heq : Π v', π (popl (ps v') = (E = prj 0 v')))
  : π ((`♡ v' : Tuple n, ¬ ⋀ dropl (ps (v' ⨾ E))) ⇒ Q)
  → π ((`♡ v : Tuple (+1 n), ¬ ⋀ (ps v)) ⇒ Q) ≔
begin
  assume n ps Q E heq hsmall hbig;
  refine hsmall (pi_to_♡ (λ v' : Tuple n, ¬ ⋀ dropl (ps (v' ⨾ E)))
    (λ v' hp,
      ♡_to_pi (λ v, ¬ ⋀ (ps v)) hbig (v' ⨾ E)
        (⋀_pop_intro (ps (v' ⨾ E))
          (=⇒ (eq_sym (heq (v' ⨾ E))) (eq_refl E))
          hp)))
end;

// NRM22: simpler unary version of NRM20 (no extra y-binder).
opaque symbol NRM22 [Q : Prop] (E : τ ι)
  : π (¬ ⊤ ⇒ Q)
  → π ((`♡ v : Tuple 1, ¬ ⋀ (∎ ∷ ⊤ ∷ (prj 0 v = E))) ⇒ Q) ≔
begin
  assume Q E h1 h2;
  refine h1 (λ ht,
    ♡_to_pi (λ v : Tuple 1, ¬ ⋀ (∎ ∷ ⊤ ∷ (prj 0 v = E)))
            h2 (unit ⨾ E)
            (⋀₂_intro ht (eq_refl E)))
end;

// NRM23: NRM22 with reversed equality.
opaque symbol NRM23 [Q : Prop] (E : τ ι)
  : π (¬ ⊤ ⇒ Q)
  → π ((`♡ v : Tuple 1,
         ¬ ⋀ (∎ ∷ ⊤ ∷ (E = prj 0 v))) ⇒ Q) ≔
begin
  assume Q E h1 h2;
  refine h1 (λ ht,
    ♡_to_pi (λ v : Tuple 1, ¬ ⋀ (∎ ∷ ⊤ ∷ (E = prj 0 v)))
            h2 (unit ⨾ E)
            (⋀₂_intro ht (eq_refl E)))
end;

// ---- NRM24-26: Trivial structural rules ----

// NRM24: P not of form A ∧ B; H ⊢ ♡x · ¬(⊤ ∧ P) ⇒ Q → H ⊢ ♡x · ¬P ⇒ Q
opaque symbol NRM24 [n] [P : Tuple n → Prop] [Q : Prop]
  : π ((`♡ v, ¬ ⋀ (∎ ∷ ⊤ ∷ P v)) ⇒ Q)
  → π ((`♡ v, ¬ (P v)) ⇒ Q) ≔
begin
  assume n P Q h1 h2;
  refine h1 (pi_to_♡ (λ v, ¬ ⋀ (∎ ∷ ⊤ ∷ P v))
    (λ v htpv, ♡_to_pi (λ v', ¬ (P v')) h2 v (⋀₂_snd htpv)))
end;

// NRM25: x not free in P; H ⊢ P → H ⊢ ♡(x) · P
//   = forall2(x).P in PP notation. `pi_to_♡` with constant predicate
//   (the body doesn't depend on the bound tuple).
opaque symbol NRM25 [n] [P : Prop] [Q : Prop]
  : π (P ⇒ Q)
  → π ((`♡ _ : Tuple n, P) ⇒ Q) ≔
begin
  assume n P Q hp h♡;
  refine hp (♡_to_pi (λ _, P) h♡ (inh_tuple [n]))
end;

// NRM26: y not free in P; H ⊢ ♡(x,...) · P → H ⊢ ♡(x,y,...) · P
// Helper: prepend an element to a Tuple n.
symbol tuple_prepend [n] : τ ι → Tuple n → Tuple (+1 n);
rule tuple_prepend [0] $x unit ↪ unit ⨾ $x
with tuple_prepend [+1 $n] $x ($w ⨾ $y) ↪ tuple_prepend [$n] $x $w ⨾ $y;

opaque symbol NRM26 [n] [P : Tuple (+1 n) → Prop] [Q : Prop]
  : π ((`♡ v' : Tuple n, P (tuple_prepend 𝟎 v')) ⇒ Q)
  → π ((`♡ v : Tuple (+1 n), P v) ⇒ Q) ≔
begin
  assume n P Q hp h♡;
  refine hp (pi_to_♡ (λ v', P (tuple_prepend 𝟎 v'))
    (λ v', ♡_to_pi (λ v, P v) h♡ (tuple_prepend 𝟎 v')))
end;

// ---- NRM27-30: Arithmetic solver dispatch ----
//
// PP's solver closes a universal hypothesis `♡(x₁,…,xₙ)·¬(P ∧ … ∧ Q)`
// when the conjunction holds two bounding inequalities `a + xᵢ ≤ 𝟎` and
// `b − xᵢ ≤ 𝟎` with `solveur(a + b) = 𝟎`: those force `xᵢ = b`, and the
// substituted conjunction `[xᵢ := b](P ∧ … ∧ Q)` is satisfiable, so the
// universal-of-negation is *false* and discharges the sequent.
//
// In LP this is an INS-style contradiction: the hypothesis is refuted at
// the solver's witness point.  We instantiate the `♡`-binder at the
// canonical zero tuple — the solver substitution evaluates there — and
// take the witnessing conjunction proof `π (P 𝟎⃗)` as a solver-confirmed
// side condition (`trust`, exactly as INS / AR2 arithmetic conjuncts do).
// The continuation `h` is the (re-expanded `⊤`-normalised) child the
// replay still records; the contradiction makes it vacuous.
//
//   NRM27 / NRM29 — multi-binder (♡-block) forms, drop one binder.
//   NRM28 / NRM30 — unary (♡x) forms, drop the binder entirely.
//   27/28 are the `xᵢ = 𝟎` specialisation (a = b = 𝟎) of 29/30.

// Canonical all-zeros tuple — the solver witness point.  (`inh_tuple`
// fills with the abstract `inh`; here we need the numeral 𝟎.)
symbol zeros [n] : Tuple n;
rule zeros [0]      ↪ unit
with zeros [+1 $n]  ↪ zeros [$n] ⨾ 𝟎;

// NRM29: multi-binder, general bounds.  Refute `♡v·¬(P v)` at 𝟎⃗.
opaque symbol NRM29 [n] [P : Tuple (+1 n) → Prop] [G : Prop]
  (hw : π (P (zeros [+1 n])))
  (h  : π ((`♡ _ : Tuple n, ¬ ⊤) ⇒ G))
  : π ((`♡ v : Tuple (+1 n), ¬ (P v)) ⇒ G) ≔
begin
  assume n P G hw h h♡;
  refine ⊥ₑ (♡_to_pi (λ v, ¬ (P v)) h♡ (zeros [+1 n]) hw)
end;

// NRM27: bare goal (no `⇒R`), `xᵢ = 𝟎` specialisation.  The goal
// `♡v·¬(P v)` reduces to `♢v'·¬(R v')` where `R = [xᵢ := 𝟎]P` drops the
// pinned binder.  `P v ⟹ R (drop v)` (the bounds force xᵢ = 𝟎) is the
// solver-confirmed bridge; with it, `R` unsatisfiable ⟹ `P` unsatisfiable.
// Untriggered in the corpus — stated to the spec shape, `bridge` `trust`ed.
opaque symbol NRM27 [n] [P : Tuple (+1 n) → Prop] [R : Tuple n → Prop]
  (bridge : Π v : Tuple (+1 n), π (P v) → π (R (drop [1] [n] v)))
  (h : π (`♢ v' : Tuple n, ¬ (R v')))
  : π (`♡ v : Tuple (+1 n), ¬ (P v)) ≔
begin
  assume n P R bridge h;
  refine pi_to_♡ (λ v, ¬ (P v))
    (λ v hp, ♢_to_pi (λ v', ¬ (R v')) h (drop [1] [n] v) (bridge v hp))
end;

// NRM30: unary binder, general bounds.  Drop the binder entirely.
opaque symbol NRM30 [P : τ ι → Prop] [G : Prop]
  (hw : π (P 𝟎))
  (h  : π (¬ ⊤ ⇒ G))
  : π ((`♡ v : Tuple 1, ¬ (P (prj 0 v))) ⇒ G) ≔
begin
  assume P G hw h h♡;
  refine ⊥ₑ (♡_to_pi (λ v, ¬ (P (prj 0 v))) h♡ (unit ⨾ 𝟎) hw)
end;

// NRM28: `x = 𝟎` specialisation of NRM30 (same shape, same proof).
opaque symbol NRM28 [P : τ ι → Prop] [G : Prop]
  (hw : π (P 𝟎))
  (h  : π (¬ ⊤ ⇒ G))
  : π ((`♡ v : Tuple 1, ¬ (P (prj 0 v))) ⇒ G) ≔
begin
  assume P G hw h h♡;
  refine ⊥ₑ (♡_to_pi (λ v, ¬ (P (prj 0 v))) h♡ (unit ⨾ 𝟎) hw)
end;

// ---- `_1` (Result-form) variants — §8.13 ----
//
// Per discussion, no NRM_1 rules are emitted in the current corpus.
// NRM1_1 is the lone exception — it strips a constant ♢-binder via
// `nrm1_eq`, mirroring NRM1's role at the chain level.

symbol NRM1_1 [n] [P Q : Prop]
  (r : Res (P ⇒ Q)) : Res ((`♢ _ : Tuple n, P) ⇒ Q)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm1_eq n P Q) (res_eq r));

// NRM14_1 — chain (Res) form of NRM14.  PP leaves NRM rules *unprimed* in the
// first-normalisation chain (unlike ALL7/ALL9/STOP/IMP), so the emitter maps a
// chain-context `NRM14` to this; `nrm14_eq` (Res.lp) is the bridge equality.
symbol NRM14_1 [n] [P : Tuple n → Prop] [R : Prop]
  (r : Res ((`♡ v, ¬ ⋀_snoc ⊤ (P v)) ⇒ R)) : Res ((`♢ v, ¬ (P v)) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm14_eq n P R) (res_eq r));
