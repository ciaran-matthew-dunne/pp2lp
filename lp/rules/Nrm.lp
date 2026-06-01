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
symbol NRM5 [n] [P Q R : Tuple n → Prop] [S : Prop]
  : π ((`♢ v, ⋀_snoc (P v) (Q v) ⇒ R v) ⇒ S)
  → π ((`♢ v, P v ⇒ Q v ⇒ R v) ⇒ S);

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
  admit;
  //assume n P Q R h1 h2;
  //refine h1 (pi_to_♡ (λ v, ¬ ⋀ (∎ ∷ P v ∷ Q v))
  //  (λ v hpq, ♢_to_pi (λ v', ⋀ (∎ ∷ P v' ∷ Q v') ⇒ ⊥) h2 v hpq))
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
// PP's left-associative ∧ puts the equality `x = E` *first* — at the head of
// the snoc list — so the conclusion pushes it onto the front of the rest `ps`
// with `pushl`.  The premise drops it and substitutes x := E (`ps (v' ⨾ E)`).
// `⋀_push_front` re-adds the head conjunct to recover the full goal; after the
// substitution `prj 0 (v' ⨾ E) ↪ E`, so it discharges as `eq_refl E`.
opaque symbol NRM20 [n] [ps : Tuple (+1 n) → 𝕃* o] [Q : Prop] (E : τ ι)
  : π ((`♡ v' : Tuple n, ¬ ⋀ ps (v' ⨾ E)) ⇒ Q)
  → π ((`♡ v : Tuple (+1 n), ¬ ⋀ pushl (prj 0 v = E) (ps v)) ⇒ Q) ≔
begin
  assume n ps Q E h1 h2;
  refine h1 (pi_to_♡ _
    (λ v' hp,
      ♡_to_pi (λ v, ¬ ⋀ pushl (prj 0 v = E) (ps v)) h2 (v' ⨾ E)
        (⋀_push_front (prj 0 (v' ⨾ E) = E) (ps (v' ⨾ E)) (eq_refl E) hp)))
end;

// NRM21: dual to NRM20 — equality reversed.
opaque symbol NRM21 [n] [P : Tuple (+1 n) → Prop] [Q : Prop] (E : τ ι)
  : π ((`♡ y : Tuple n, ¬ (P (y ⨾ E))) ⇒ Q)
  → π ((`♡ v : Tuple (+1 n),
         ¬ ⋀ (∎ ∷ P v ∷ (E = prj 0 v))) ⇒ Q) ≔
begin
  assume n P Q E h1 h2;
  refine h1 (pi_to_♡ (λ y, ¬ (P (y ⨾ E)))
    (λ y hpy,
      ♡_to_pi (λ v, ¬ ⋀ (∎ ∷ P v ∷ (E = prj 0 v))) h2 (y ⨾ E)
        (⋀₂_intro hpy (eq_refl E))))
end;

// NRM22: simpler unary version of NRM20 (no extra y-binder).
opaque symbol NRM22 [P : τ ι → Prop] [Q : Prop] (E : τ ι)
  : π (¬ (P E) ⇒ Q)
  → π ((`♡ v : Tuple 1,
         ¬ ⋀ (∎ ∷ P (prj 0 v) ∷ (prj 0 v = E))) ⇒ Q) ≔
begin
  assume P Q E h1 h2;
  refine h1 (λ hpe,
    ♡_to_pi (λ v : Tuple 1, ¬ ⋀ (∎ ∷ P (prj 0 v) ∷ (prj 0 v = E)))
            h2 (unit ⨾ E)
            (⋀₂_intro hpe (eq_refl E)))
end;

// NRM23: NRM22 with reversed equality.
opaque symbol NRM23 [P : τ ι → Prop] [Q : Prop] (E : τ ι)
  : π (¬ (P E) ⇒ Q)
  → π ((`♡ v : Tuple 1,
         ¬ ⋀ (∎ ∷ P (prj 0 v) ∷ (E = prj 0 v))) ⇒ Q) ≔
begin
  assume P Q E h1 h2;
  refine h1 (λ hpe,
    ♡_to_pi (λ v : Tuple 1, ¬ ⋀ (∎ ∷ P (prj 0 v) ∷ (E = prj 0 v)))
            h2 (unit ⨾ E)
            (⋀₂_intro hpe (eq_refl E)))
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
opaque symbol NRM25 [n] [P : Prop]
  : π P → π (`♡ _ : Tuple n, P) ≔
begin
  assume n P hp;
  refine pi_to_♡ (λ _ : Tuple n, P) (λ _, hp)
end;

// NRM26: y not free in P; H ⊢ ♡(x,...) · P → H ⊢ ♡(x,y,...) · P
//   = extend the binder with a y not appearing in P. The body
//   ignores the new variable.

// Helper: drop the last element of a Tuple (+1 n).
symbol nrm26_drop_last [n] : Tuple (+1 n) → Tuple n;
rule nrm26_drop_last [$n] ($w ⨾ _) ↪ $w;

// Helper: produce P (drop_last v) from a per-tuple-n proof of P.
//   Stays !!-typed so the rewrite rule fires; rule body transports
//   from ♡ via `♡_eq_!!`.
symbol nrm26_drop_proof [n] (P : Tuple n → Prop)
  : π (`!! w, P w)
  → Π v : Tuple (+1 n), π (P (nrm26_drop_last v));
rule nrm26_drop_proof [$n] $P $h ($w ⨾ _) ↪ !!_to_pi $P $h $w;

opaque symbol NRM26 [n] [P : Tuple n → Prop]
  : π (`♡ v, P v)
  → π (`♡ v : Tuple (+1 n), P (nrm26_drop_last v)) ≔
begin
  assume n P h;
  refine pi_to_♡ (λ v : Tuple (+1 n), P (nrm26_drop_last v))
    (nrm26_drop_proof P (=⇒ (♡_eq_!! P) h))
end;

// ---- NRM27-30: Arithmetic solver dispatch ----
//
// These rules encode arithmetic solver outputs. Their full encoding
// requires arithmetic-solver infrastructure (see Arith.lp's solver
// rules). Stubs for now.
//
// NRM27: (xᵢ ≤ 0) and (−xᵢ ≤ 0) in conjunction; R = [xᵢ := 0]…
//   → ♢… · ¬R  ⊢  ♡(x₁,...,xₙ) · ¬(P ∧ ⋯ ∧ Q)
// NRM28-30: variants with solver dispatch.
// TODO: implement once Arith.lp solver rules are wired.

// ---- `_1` (Result-form) variants — §8.13 ----
//
// Per discussion, no NRM_1 rules are emitted in the current corpus.
// NRM1_1 is the lone exception — it strips a constant ♢-binder via
// `nrm1_eq`, mirroring NRM1's role at the chain level.

symbol NRM1_1 [n] [P Q : Prop]
  (r : Res (P ⇒ Q)) : Res ((`♢ _ : Tuple n, P) ⇒ Q)
  ≔ mk_1 (res_tm r) (eq_trans (@nrm1_eq n P Q) (res_eq r));
