// Normalisation (§A.12) — tuple-based encoding.
//
// Spec uses `♢` (= goal-side n-ary universal) and `♡` (= hypothesis-
// side n-ary universal). Both reduce propositionally to `!!` via the
// `♢_eq_!!` / `♡_eq_!!` lemmas in lemmas/Tuple.lp; bodies use the dedicated
// `pi_to_♢` / `♢_to_pi` (and ♡ analogues) bridges.

require open pp2lp.B pp2lp.lemmas.Int pp2lp.lemmas.Tuple pp2lp.rules.Res;

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
// Encoded with the n,m-indexed split helpers from B.lp:
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

// ---- NRM20-23: Substitution (drop a binder pinned by an equality) ----
//
// PP pins *whichever* binder an equality conjunct fixes, at *any* slot k of the
// ♡-block, with the witness E a function of the remaining binders (`#x.#y.(x=y)`
// pins x at y).  `ins`/`rm` (B.lp) splice slot k in and out and `prj_ins`
// (lemmas/Tuple.lp) is the round-trip, so one lemma — NRM20 — covers every slot;
// the emitter supplies k and E, and bubbles the pinning equality to the conjunct
// list's *tail* (`qs v ∷ eq`) first when PP places it elsewhere.  The one shape it
// does NOT route here — slot-0 head equality with block-closed E (PP's `¬(x=E ∧ …)`,
// all of prv) — takes the NRM20H fast path below, which peels the head equality
// with popl/dropl and so skips that per-site rotation.  NRM21 is the reversed-
// equality (`E = x`) orientation; NRM22/23 (below) are the unary instances PP
// emits with no surrounding block.
//
//   H ⊢ ♡v'·¬(qs[xₖ:=E v'])        H ⊢ ♡v·¬(qs ∧ (prj k v = E (rm k v)))
opaque symbol NRM20 [n] (k : ℕ) [qs : Tuple (+1 n) → 𝕃* o] [Q : Prop]
  (E : Tuple n → τ ι)
  : π ((`♡ v' : Tuple n, ¬ ⋀ (qs (ins k (E v') v'))) ⇒ Q)
  → π ((`♡ v : Tuple (+1 n), ¬ ⋀ (qs v ∷ (prj k v = E (rm k v)))) ⇒ Q) ≔
begin
  assume n k qs Q E hsmall hbig;
  refine hsmall (pi_to_♡ (λ v' : Tuple n, ¬ ⋀ (qs (ins k (E v') v')))
    (λ v' hq,
      ♡_to_pi (λ v, ¬ ⋀ (qs v ∷ (prj k v = E (rm k v)))) hbig (ins k (E v') v')
        (⋀_intro hq (prj_ins k (E v') v'))))
end;

// NRM20H: fast path for the common shape — pinning equality at the conjunct
// *head*, slot 0, E block-closed.  popl/dropl peel the head equality directly (no
// rotation), and slot 0 is a plain `v' ⨾ E` (no `ins`/`rm`).  Semantically the
// slot-0 head case of NRM20; kept separate only because the rotation NRM20 would
// need here is the per-site cost that dominates prv's NRM20-dense proofs.
opaque symbol NRM20H [n] [ps : Tuple (+1 n) → 𝕃* o] [Q : Prop] (E : τ ι)
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

// NRM21: NRM20 with the equality reversed (`E (rm k v) = prj k v`).
opaque symbol NRM21 [n] (k : ℕ) [qs : Tuple (+1 n) → 𝕃* o] [Q : Prop]
  (E : Tuple n → τ ι)
  : π ((`♡ v' : Tuple n, ¬ ⋀ (qs (ins k (E v') v'))) ⇒ Q)
  → π ((`♡ v : Tuple (+1 n), ¬ ⋀ (qs v ∷ (E (rm k v) = prj k v))) ⇒ Q) ≔
begin
  assume n k qs Q E hsmall hbig;
  refine hsmall (pi_to_♡ (λ v' : Tuple n, ¬ ⋀ (qs (ins k (E v') v')))
    (λ v' hq,
      ♡_to_pi (λ v, ¬ ⋀ (qs v ∷ (E (rm k v) = prj k v))) hbig (ins k (E v') v')
        (⋀_intro hq (eq_sym (prj_ins k (E v') v')))))
end;

// NRM22: the ♡-body's tail equality pins the binder at E (general list
// form; the ⊤-headed NRM14-fed shape is the instance ps := λ _, (∎ ∷ ⊤)).
opaque symbol NRM22 [Q : Prop] [ps : Tuple 1 → 𝕃* o] (E : τ ι)
  : π (¬ ⋀ (ps (unit ⨾ E)) ⇒ Q)
  → π ((`♡ v : Tuple 1, ¬ ⋀ (ps v ∷ (prj 0 v = E))) ⇒ Q) ≔
begin
  assume Q ps E h1 h2;
  refine h1 (λ hps,
    ♡_to_pi (λ v : Tuple 1, ¬ ⋀ (ps v ∷ (prj 0 v = E)))
            h2 (unit ⨾ E)
            (⋀_intro hps (eq_refl E)))
end;

// NRM23: NRM22 with reversed equality (⊤-headed special case; kept for the
// chain-form nrm23_eq bridge).
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

// NRM23G: the general-list reversed form (NRM22's exact mirror) — the
// main-tree emitter uses this one uniformly.
opaque symbol NRM23G [Q : Prop] [ps : Tuple 1 → 𝕃* o] (E : τ ι)
  : π (¬ ⋀ (ps (unit ⨾ E)) ⇒ Q)
  → π ((`♡ v : Tuple 1, ¬ ⋀ (ps v ∷ (E = prj 0 v))) ⇒ Q) ≔
begin
  assume Q ps E h1 h2;
  refine h1 (λ hps,
    ♡_to_pi (λ v : Tuple 1, ¬ ⋀ (ps v ∷ (E = prj 0 v)))
            h2 (unit ⨾ E)
            (⋀_intro hps (eq_refl E)))
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

// NRM26: y not free in P; H ⊢ ♡(x,…)·P → H ⊢ ♡(x,y,…)·P.  PP drops the unused
// binder at *any* slot k; one lemma covers them all — instantiate the ♡ at
// `ins k (el ι) v'`.  The dropped slot is never read, so the dummy is `el ι` (the
// canonical inhabitant), not a misleading 𝟎.  The emitter supplies k (the dropped
// var's position, read off the annotation diff against the child's binder list).
opaque symbol NRM26 [n] (k : ℕ) [P : Tuple (+1 n) → Prop] [Q : Prop]
  : π ((`♡ v' : Tuple n, P (ins k (el ι) v')) ⇒ Q)
  → π ((`♡ v : Tuple (+1 n), P v) ⇒ Q) ≔
begin
  assume n k P Q hp h♡;
  refine hp (pi_to_♡ (λ v', P (ins k (el ι) v'))
    (λ v', ♡_to_pi (λ v, P v) h♡ (ins k (el ι) v')))
end;

// ---- NRM27-30: Arithmetic solver dispatch (trust-free) ----
//
// PP's solver closes a universal hypothesis `♡(x₁,…,xₙ)·¬(P ∧ … ∧ Q)`
// when the conjunction holds two bounding inequalities `a + xᵢ ≤ 𝟎` and
// `b − xᵢ ≤ 𝟎` with `solveur(a + b) = 𝟎`: those force `xᵢ = b`, and the
// substituted conjunction `[xᵢ := b](P ∧ … ∧ Q)` is satisfiable, so the
// universal-of-negation is *false* and discharges the sequent.
//
// One lemma, NRM29, realises all four PP rules: peel the pinned binder by
// *instantiating* the `♡`-hypothesis at the solver witness `b` (the membership
// premises the spec carries are solver bookkeeping — unused here), leaving the
// continuation `♢v'·¬⋀(ps (v' ⨾ b v')) ⇒ R`; the emitter bridges the substituted
// conjunction `⋀ (ps (v' ⨾ b v'))` to ⊤ with a generated congruence proof (each
// cancelling bound = ⊤ via `eq_true` + `leq_zero_of_sum_zero` + `prove_sum_eq`).
// NRM27/28 are the `xᵢ := 𝟎` case (b = 𝟎) and NRM30 the unary (♡x) case — the
// emitter maps all of NRM27/28/30 onto NRM29 with the matching witness.  Only
// NRM29 is corpus-triggered (apero); the others have no replay.

// ---- helper lemmas for the trust-free solver dispatch ----

// `P` provably true ⟹ `P = ⊤`, so a ⋀-conjunct the solver discharges can
// be rewritten to ⊤ and absorbed by `⋀ (_ ∷ ⊤) ↪ ⋀ _`.
opaque symbol eq_true (P : Prop) : π P → π (P = ⊤) ≔
begin
  assume P h;
  refine propExt _ _ _ _
  { assume hp; refine ⊤ᵢ }
  { assume ht; refine h }
end;

// A sum that arithmetic-normalises to 𝟎 is ≤ 𝟎.  The emitter builds the
// `E = 𝟎` proof with `prove_sum_eq` (add_comm/assoc/opp cancellation).
opaque symbol leq_zero_of_sum_zero (E : τ ι) : π (E = 𝟎) → π (leq E 𝟎) ≔
begin
  assume E h;
  rewrite h;
  refine leq_refl 𝟎
end;

// NRM29: multi-binder, pin the prj0 slot to `b v'` (witness a function of
// the remaining binders — e.g. b v' = — prj 0 v' for the sum-zero /
// cancelling case).  The emitter supplies `b` and the ⊤-normalisation
// bridge for the substituted conjunction `⋀ (ps (v' ⨾ b v'))`.
opaque symbol NRM29 [n] [ps : Tuple (+1 n) → 𝕃* o] [R : Prop] (b : Tuple n → τ ι)
  : π ((`♢ v' : Tuple n, ¬ ⋀ (ps (v' ⨾ b v'))) ⇒ R)
  → π ((`♡ v : Tuple (+1 n), ¬ ⋀ (ps v)) ⇒ R) ≔
begin
  assume n ps R b h_prem h♡;
  refine h_prem (pi_to_♢ (λ v', ¬ ⋀ (ps (v' ⨾ b v')))
    (λ v', ♡_to_pi (λ v, ¬ ⋀ (ps v)) h♡ (v' ⨾ b v')))
end;

// ---- `_1` (Result-form) variants — §8.13 ----
//
// PP leaves NRM rules *unprimed* in the first-normalisation chain (unlike
// ALL7/ALL9/STOP/IMP), so the emitter primes a chain-context `NRM<k>` to
// `NRM<k>_1` (`Emit_ctx.chain_emit_name`).  Each chain form lifts the base
// rule's premise→conclusion implication to a `Res`-to-`Res` map through a
// bridge equality `nrm<k>_eq : conclusion = premise`; the body is the uniform
// `mk_1 (res_tm r) (eq_trans (@nrm<k>_eq …) (res_eq r))`.  Every NRM rule that
// can appear in a Res chain needs one (see CLAUDE.md: emitting an undefined
// `NRM<k>_1` shows up as a lambdapi "Unknown symbol", not a fail-loud emit).

symbol NRM1_1 [n] [P Q : Prop]
  (r : Res (P ⇒ Q)) : Res ((`♢ _ : Tuple n, P) ⇒ Q)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm1_eq n P Q) (res_eq r));

// NRM2 bridge (evidence form).  PP's chain NRM2 weakens the ♢-body by a v-free
// hypothesis P (`(♢v·Q v) ⇒ S  ↦  (♢v·(P⇒Q v)) ⇒ S`), sound only given a proof
// of P: under `hp : π P` the body equivalence `(P⇒Q v) ⟺ Q v` holds, lifted
// under the ♢ by `!!_cong`.  Unlike the unconditional nrmK_eq bridges this
// takes `hp`, so the emitter must supply it (translate.ml NRM2 chain dispatch).
opaque symbol nrm2_eq [n] [P : Prop] [Q : Tuple n → Prop] [S : Prop] (hp : π P)
  : π (((`♢ v, P ⇒ Q v) ⇒ S) = ((`♢ v, Q v) ⇒ S)) ≔
begin
  assume n P Q S hp;
  have hbody : Π v, π ((P ⇒ Q v) = (Q v))
    { assume v; refine propExt _ _ (λ hpq, hpq hp) (λ hq _, hq) };
  have hpred : π ((`♢ v, P ⇒ Q v) = (`♢ v, Q v))
    { refine eq_trans (♢_eq_!! (λ v, P ⇒ Q v))
        (eq_trans (!!_cong hbody) (eq_sym (♢_eq_!! (λ v, Q v)))) };
  rewrite hpred; reflexivity
end;

// NRM2_1 — chain (Res) form of NRM2, via the evidence-form `nrm2_eq` above.
symbol NRM2_1 [n] [P : Prop] [Q : Tuple n → Prop] [S : Prop] (hp : π P)
  (r : Res ((`♢ v, Q v) ⇒ S)) : Res ((`♢ v, P ⇒ Q v) ⇒ S)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm2_eq n P Q S hp) (res_eq r));

// NRM14_1 — chain (Res) form of NRM14.  PP leaves NRM rules *unprimed* in the
// first-normalisation chain (unlike ALL7/ALL9/STOP/IMP), so the emitter maps a
// chain-context `NRM14` to this; `nrm14_eq` (Res.lp) is the bridge equality.
symbol NRM14_1 [n] [P : Tuple n → Prop] [R : Prop]
  (r : Res ((`♡ v, ¬ ⋀_snoc ⊤ (P v)) ⇒ R)) : Res ((`♢ v, ¬ (P v)) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm14_eq n P R) (res_eq r));

// NRM13_1 — chain (Res) form of NRM13, via the `nrm13_eq` bridge (Res.lp).
symbol NRM13_1 [n] [P Q : Tuple n → Prop] [R : Prop]
  (r : Res ((`♡ v, ¬ ⋀_snoc (P v) (¬ Q v)) ⇒ R)) : Res ((`♢ v, P v ⇒ Q v) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm13_eq n P Q R) (res_eq r));

// NRM12_1 — chain (Res) form of NRM12, via the `nrm12_eq` bridge (Res.lp).
symbol NRM12_1 [n] [P Q : Tuple n → Prop] [R : Prop]
  (r : Res ((`♡ v, ¬ ⋀_snoc (P v) (Q v)) ⇒ R)) : Res ((`♢ v, P v ⇒ ¬ (Q v)) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm12_eq n P Q R) (res_eq r));

// NRM15_1 — chain (Res) form of NRM15, via the `nrm15_eq` bridge (Res.lp).
symbol NRM15_1 [n] [P : Tuple n → Prop] [R : Prop]
  (r : Res ((`♡ v, ¬ ⋀_snoc ⊤ (¬ (P v))) ⇒ R)) : Res ((`♢ v, P v) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm15_eq n P R) (res_eq r));

// NRM5_1 — chain (Res) form of NRM5, via the `nrm5_eq` bridge (Res.lp).
symbol NRM5_1 [n] [P Q R : Tuple n → Prop] [S : Prop]
  (r : Res ((`♢ v, ⋀_snoc (P v) (Q v) ⇒ R v) ⇒ S))
  : Res ((`♢ v, P v ⇒ Q v ⇒ R v) ⇒ S)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm5_eq n P Q R S) (res_eq r));

// NRM10_1 — chain (Res) form of NRM10, via the `nrm10_eq` bridge (Res.lp).
symbol NRM10_1 [n] [Ps : Tuple n → 𝕃* o] [Q : Tuple n → Prop] [R : Prop]
  (r : Res ((`♡ v, ¬ ⋀ (Ps v ∷ Q v)) ⇒ R))
  : Res ((`♢ v, ⋀ (Ps v ∷ Q v) ⇒ ⊥) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm10_eq n Ps Q R) (res_eq r));

// NRM24_1 — chain (Res) form of NRM24, via the `nrm24_eq` bridge (Res.lp).
symbol NRM24_1 [n] [P : Tuple n → Prop] [Q : Prop]
  (r : Res ((`♡ v, ¬ ⋀ (∎ ∷ ⊤ ∷ P v)) ⇒ Q))
  : Res ((`♡ v, ¬ (P v)) ⇒ Q)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm24_eq n P Q) (res_eq r));

// NRM3 bridge: ((♢v·(P v ⇒ Q)) ⇒ S) = ((Q ⇒ S) ∧ ((∀v·¬P v) ⇒ S)), Q is v-free.
// (Lives here, not Res.lp, because the ⇐ direction reuses NRM3 itself; the ⇒
// direction builds the ♢ witness from Q, or vacuously from ¬P v.)
opaque symbol nrm3_eq [n] [P : Tuple n → Prop] [Q S : Prop]
  : π (((`♢ v, P v ⇒ Q) ⇒ S) = ⋀_snoc (Q ⇒ S) ((`!! v, ¬ (P v)) ⇒ S)) ≔
begin
  assume n P Q S;
  refine propExt _ _
    (λ hres, ⋀₂_intro
       (λ hq, hres (pi_to_♢ (λ v, P v ⇒ Q) (λ v hpv, hq)))
       (λ hnp, hres (pi_to_♢ (λ v, P v ⇒ Q)
                       (λ v hpv, ⊥ₑ (!!_to_pi (λ v, ¬ (P v)) hnp v hpv)))))
    (λ hprem, @NRM3 n P Q S hprem)
end;

// NRM3_1 — chain (Res) form of NRM3, via the `nrm3_eq` bridge above.  The
// premise is the snoc-conjunction the emitter discharges with AND4_1.
symbol NRM3_1 [n] [P : Tuple n → Prop] [Q S : Prop]
  (r : Res (⋀_snoc (Q ⇒ S) ((`!! v, ¬ (P v)) ⇒ S))) : Res ((`♢ v, P v ⇒ Q) ⇒ S)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm3_eq n P Q S) (res_eq r));

// NRM23_1 — chain (Res) form of NRM23, via the `nrm23_eq` bridge (Res.lp).  E is
// implicit here (the emitter emits `NRM23_1 _`, inferring E from the Res target).
symbol NRM23_1 [Q : Prop] [E : τ ι]
  (r : Res (¬ ⊤ ⇒ Q))
  : Res ((`♡ v : Tuple 1, ¬ ⋀ (∎ ∷ ⊤ ∷ (E = prj 0 v))) ⇒ Q)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm23_eq Q E) (res_eq r));

// NRM22_1 — chain (Res) form of NRM22, via the general `nrm22_eq` bridge
// (Res.lp): the body's tail equality pins the binder at E.
symbol NRM22_1 [Q : Prop] [ps : Tuple 1 → 𝕃* o] [E : τ ι]
  (r : Res (¬ ⋀ (ps (unit ⨾ E)) ⇒ Q))
  : Res ((`♡ v : Tuple 1, ¬ ⋀ (ps v ∷ (prj 0 v = E))) ⇒ Q)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm22_eq Q ps E) (res_eq r));

// NRM4_1 — chain (Res) form of NRM4, via the `nrm4_eq` bridge (Res.lp).
symbol NRM4_1 [n] [P R : Tuple n → Prop] [Q S : Prop]
  (r : Res ((Q ⇒ (`♢ v, P v ⇒ R v)) ⇒ S))
  : Res ((`♢ v, P v ⇒ Q ⇒ R v) ⇒ S)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm4_eq n P R Q S) (res_eq r));

// NRM7_1 — chain (Res) form of NRM7, via the `nrm7_eq` bridge (Res.lp).
symbol NRM7_1 [n] [Qs : Tuple n → 𝕃* o] [P : Tuple n → Prop] [S : Prop]
  (r : Res ((`♢ v, ⋀ (Qs v)) ⇒ ((`♢ v, P v) ⇒ S)))
  : Res ((`♢ v, ⋀ (Qs v ∷ P v)) ⇒ S)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm7_eq n Qs P S) (res_eq r));

// NRM11_1 — chain (Res) form of NRM11, via the `nrm11_eq` bridge (Res.lp).
symbol NRM11_1 [n] [P : Tuple n → Prop] [R : Prop]
  (r : Res ((`♡ v, ¬ ⋀_snoc ⊤ (P v)) ⇒ R))
  : Res ((`♢ v, P v ⇒ ⊥) ⇒ R)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm11_eq n P R) (res_eq r));

// NRM25_1 — chain (Res) form of NRM25, via the `nrm25_eq` bridge (Res.lp).
symbol NRM25_1 [n] [P Q : Prop]
  (r : Res (P ⇒ Q))
  : Res ((`♡ _ : Tuple n, P) ⇒ Q)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm25_eq n P Q) (res_eq r));

// NRM8_1 — chain (Res) form of NRM8, via the `nrm8_eq` bridge (Res.lp).
symbol NRM8_1 [n m] [Q : Tuple n → Tuple m → Prop] [S : Prop]
  (r : Res ((`♢ v : Tuple (n ++ m), Q (take [n] [m] v) (drop [n] [m] v)) ⇒ S))
  : Res ((`♢ x : Tuple n, `!! y : Tuple m, Q x y) ⇒ S)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm8_eq n m Q S) (res_eq r));

// NRM9_1 — chain (Res) form of NRM9, via the `nrm9_eq` bridge (Res.lp).
symbol NRM9_1 [n m] [P : Tuple n → Prop] [Q : Tuple n → Tuple m → Prop] [S : Prop]
  (r : Res ((`♢ v : Tuple (n ++ m),
              P (take [n] [m] v) ⇒ Q (take [n] [m] v) (drop [n] [m] v)) ⇒ S))
  : Res ((`♢ x : Tuple n, P x ⇒ (`!! y : Tuple m, Q x y)) ⇒ S)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm9_eq n m P Q S) (res_eq r));

// NRM6_1 — chain (Res) form of NRM6, via the `nrm6_eq` bridge (Res.lp).
symbol NRM6_1 [n] [Qs : Tuple n → 𝕃* o] [P R : Tuple n → Prop] [S : Prop]
  (r : Res ((`♢ v, R v ⇒ ⋀ (Qs v)) ⇒ ((`♢ v, R v ⇒ P v) ⇒ S)))
  : Res ((`♢ v, R v ⇒ ⋀ (Qs v ∷ P v)) ⇒ S)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm6_eq n Qs P R S) (res_eq r));

// NRM19_1 — chain (Res) form of NRM19 (a Witness_hyp *discharge*, not a
// transport).  Given the witness v and the in-scope hyp `R v`, the antecedent
// `♡u·¬(⊤∧R u)` is refuted (at u := v), so the implication is provable and
// `mk_0 ∘ prop_eq_top` seeds the Res at ⊤ — the AXM8_1/AXM9_1 seed pattern.  The
// emitter recovers (v, hr) with the same [find_nrm19_match] the base rule uses.
symbol NRM19_1 [n] [Q : Prop] [R : Tuple n → Prop] (v : Tuple n) (hr : π (R v))
  : Res ((`♡ u, ¬ ⋀_snoc ⊤ (R u)) ⇒ Q)
  ≔ mk_0 (prop_eq_top (NRM19 v hr));
