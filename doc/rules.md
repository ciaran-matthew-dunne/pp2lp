# Annexe A — Inference rules used by PP

Cross-referenced against `doc/rules.pdf` (Annexe A, pp. 101-119). Antecedents and consequents below are translated from the French PDF; the rule shapes themselves match the spec.

## Notation

| Glyph | Meaning |
|-------|---------|
| `H ⊢ P` | Sequent: hypotheses H, conclusion P. |
| `⇝` | "yields result". |
| `♢` | n-ary universal, goal-side (`forall` in PP source; rendered `♢` in LP). |
| `♡` | n-ary universal, hypothesis-side (`forall2` in PP source; rendered `♡` in LP). |
| `∀` (single-var) | encoded as `!!` over `Tuple 1` in LP. |
| `∃` | encoded as `??` in LP. |
| VRAI / FAUX | PP's `TRUE` / `FALSE` (kept verbatim from PP's wire format; `B.lp` aliases them to `⊤` / `⊥`). |
| `≪` | spec's "much-less-than"; `B.lp` aliases `≪ ≔ ≤` since PP never emits `≪`. |
| `†` | rule has an α-renaming variant in the spec when the bound variable clashes; the LP encoding handles this at parse time, so a single LP rule covers both. |

## Status legend

The **Status** column in each table uses one of:

| Value | Meaning |
|-------|---------|
| `proved` | Closed in LP (no `admit`); emitter passes proper proof terms. |
| `proved · emit-trust` | LP rule is closed, but the emitter passes `trust` for one or more arguments at use sites (because PP's side-condition is solver-confirmed or boolean-membership-style; see Notes). |
| `proved · partial-emit` | LP rule is closed for supported shapes, but the emitter rejects unsupported shapes instead of using whole-goal `trust`. |
| `admit` | LP rule has an open `admit` — known gap, not yet closed. |
| `phantom` | LP rule defined for completeness but never applied by the emitter (PP emits the rule only as a no-op). |
| `not-impl` | No LP rule. The trace-first emitter should reject or skip these explicitly until they are formalized. |

## Status summary

```
proved · emit-trust    AR2–AR9, AR13, INS, BOOL31–42
proved · emitted       NRM20, NRM22
proved · partial-emit  NRM21, NRM23   (unexercised; shape unverified vs replays)
phantom                AR10, AR3_F
not-impl               NRM27, NRM28, NRM29, NRM29_1, NRM30, NRM30_1
```

## A.1 Conjunction — `lp/rules/Conj.lp`

| Rule | Antecedents | Consequent | LP type | Status | Notes |
|------|-------------|------------|---------|--------|-------|
| AND1 | H ⊢ ¬Q ⇒ R; H ⊢ ¬P ⇒ R | H ⊢ ¬(P ∧ Q) ⇒ R | `π (¬ Q ⇒ R) → π (¬ P ⇒ R) → π (¬ (P ∧ Q) ⇒ R)` | proved | |
| AND2 | H ⊢ P ⇒ ¬Q | H ⊢ ¬(P ∧ Q) | `π (P ⇒ ¬ Q) → π (¬ (P ∧ Q))` | proved | |
| AND3 | H ⊢ P ⇒ (Q ⇒ R) | H ⊢ (P ∧ Q) ⇒ R | `π (P ⇒ (Q ⇒ R)) → π ((P ∧ Q) ⇒ R)` | proved | |
| AND4 | H ⊢ Q; H ⊢ P | H ⊢ P ∧ Q | `π Q → π P → π (P ∧ Q)` | proved | |
| AND5 | P ∧ ··· contains A; H ⊢ P ∧ ··· ∧ B ∧ ··· ⇒ R | H ⊢ P ∧ ··· ∧ (A ⇒ B) ∧ ··· ⇒ R | `(π C → π C') → π (C' ⇒ r) → π (C ⇒ r)` | proved | Emitter rewrites antecedent congruence (`ante_cong`). |

## A.2 Disjunctions — `lp/rules/Disj.lp`

| Rule | Antecedents | Consequent | LP type | Status | Notes |
|------|-------------|------------|---------|--------|-------|
| OR1 | H ⊢ ¬P ⇒ (¬Q ⇒ R) | H ⊢ ¬(P ∨ Q) ⇒ R | `π (¬ P ⇒ (¬ Q ⇒ R)) → π (¬ (P ∨ Q) ⇒ R)` | proved | |
| OR2 | H ⊢ ¬Q; H ⊢ ¬P | H ⊢ ¬(P ∨ Q) | `π (¬ Q) → π (¬ P) → π (¬ (P ∨ Q))` | proved | |
| OR3 | H ⊢ Q ⇒ R; H ⊢ P ⇒ R | H ⊢ (P ∨ Q) ⇒ R | `π (Q ⇒ R) → π (P ⇒ R) → π ((P ∨ Q) ⇒ R)` | proved | |
| OR4 | H ⊢ ¬P ⇒ Q | H ⊢ P ∨ Q | `π (¬ P ⇒ Q) → π (P ∨ Q)` | proved | |

## A.3 Implications — `lp/rules/Impl.lp`

| Rule | Antecedents | Consequent | LP type | Status | Notes |
|------|-------------|------------|---------|--------|-------|
| IMP1 | H ⊢ P ⇒ (¬Q ⇒ R) | H ⊢ ¬(P ⇒ Q) ⇒ R | `π (P ⇒ (¬ Q ⇒ R)) → π (¬ (P ⇒ Q) ⇒ R)` | proved | |
| IMP2 | H ⊢ ¬Q; H ⊢ P | H ⊢ ¬(P ⇒ Q) | `π (¬ Q) → π P → π (¬ (P ⇒ Q))` | proved | |
| IMP3 | H ⊢ Q ⇒ R; H ⊢ ¬P ⇒ R | H ⊢ (P ⇒ Q) ⇒ R | `π (Q ⇒ R) → π (¬ P ⇒ R) → π ((P ⇒ Q) ⇒ R)` | proved | |
| IMP4 | H, P ⊢ Q | H ⊢ P ⇒ Q | `(π P → π Q) → π (P ⇒ Q)` | proved | HOAS identity (LP `λ`); emitter pushes `assume hN`. |
| IMP5 | P in H; H ⊢ Q | H ⊢ P ⇒ Q | `π Q → π (P ⇒ Q)` | proved | Emitter resolves the hyp by lookup (`emit_args:hyp`). |

| Rule | Antecedents | Consequent | Result | LP type | Status | Notes |
|------|-------------|------------|--------|---------|--------|-------|
| IMP4' | (H, P ⊢ Q) ⇝ R | H ⊢ P ⇒ Q | P ⇒ R | `Res Q → Res (P ⇒ Q)` | proved | `IMP4_1` in `lp/rules/Res.lp`. |

## A.4 Equivalence — `lp/rules/Equiv.lp`

| Rule | Antecedents | Consequent | LP type | Status | Notes |
|------|-------------|------------|---------|--------|-------|
| EQV1 | H ⊢ P ⇒ (¬Q ⇒ R); H ⊢ ¬P ⇒ (Q ⇒ R) | H ⊢ ¬(P ⇔ Q) ⇒ R | `π (P ⇒ (¬ Q ⇒ R)) → π (¬ P ⇒ (Q ⇒ R)) → π (¬ (P ⇔ Q) ⇒ R)` | proved | |
| EQV2 | H ⊢ P ⇒ ¬Q; H ⊢ ¬Q ⇒ P | H ⊢ ¬(P ⇔ Q) | `π (P ⇒ ¬ Q) → π (¬ Q ⇒ P) → π (¬ (P ⇔ Q))` | proved | |
| EQV3 | H ⊢ P ⇒ (Q ⇒ R); H ⊢ ¬P ⇒ (¬Q ⇒ R) | H ⊢ (P ⇔ Q) ⇒ R | `π (P ⇒ (Q ⇒ R)) → π (¬ P ⇒ (¬ Q ⇒ R)) → π ((P ⇔ Q) ⇒ R)` | proved | |
| EQV4 | H ⊢ P ⇒ Q; H ⊢ Q ⇒ P | H ⊢ P ⇔ Q | `π (P ⇒ Q) → π (Q ⇒ P) → π (P ⇔ Q)` | proved | |

## A.5 Negations — `lp/rules/Neg.lp`

| Rule | Antecedents | Consequent | LP type | Status | Notes |
|------|-------------|------------|---------|--------|-------|
| NOT1 | H ⊢ P ⇒ R | H ⊢ ¬¬P ⇒ R | `π (P ⇒ R) → π (¬ ¬ P ⇒ R)` | proved | |
| NOT2 | H ⊢ P | H ⊢ ¬¬P | `π P → π (¬ ¬ P)` | proved | |

## A.6 Axioms — `lp/rules/Axm.lp`

| Rule | Antecedents | Consequent | LP type | Status | Notes |
|------|-------------|------------|---------|--------|-------|
| AXM1 | ¬P in H | H ⊢ P ⇒ Q | `π (¬ P) → π (P ⇒ Q)` | proved | Hyp resolved by lookup. |
| AXM2 | P in H | H ⊢ ¬P ⇒ Q | `π P → π (¬ P ⇒ Q)` | proved | Hyp resolved by lookup. |
| AXM3 | P in H | H ⊢ P | `π P → π P` | proved | Hyp resolved by lookup. |
| AXM4 | R in H | H ⊢ P ⇒ R | `π R → π (P ⇒ R)` | proved | Hyp resolved by lookup. |
| AXM5 | ¬Q in H | H ⊢ P ⇒ (Q ⇒ R) | `π (¬ Q) → π (P ⇒ (Q ⇒ R))` | proved | Hyp resolved by lookup. |
| AXM6 | Q in H | H ⊢ P ⇒ (¬Q ⇒ R) | `π Q → π (P ⇒ (¬ Q ⇒ R))` | proved | Hyp resolved by lookup. |
| AXM7 | *(none)* | H ⊢ P ⇒ P | `π (P ⇒ P)` | proved | |
| AXM8 | P ∧ ··· contains R | H ⊢ P ∧ ··· ⇒ R | `(π C → π r) → π (C ⇒ r)` | proved | Emitter walks the conj for the index (`emit_axm8_args`). |
| AXM9 | ∀x·¬(VRAI ∧ P) in H; ∃E with [x := E] P = R | H ⊢ R ⇒ Q | ``(v : Tuple n) → π (`!! u, ¬ (⊤ ∧ P u)) → π (P v ⇒ Q)`` | proved | Tuple-uniform; emitter pulls the witness `v` from `tuple_binders` via `find_tuple_binder`. |

## A.7 Universal quantification — `lp/rules/All.lp`

| Rule | Antecedents | Consequent | LP type | Status | Notes |
|------|-------------|------------|---------|--------|-------|
| ALL1 | x, y distinct; H ⊢ ¬(∀(x,y)·P) ⇒ R | H ⊢ ¬(∀x·∀y·P) ⇒ R | ``π (¬ (`!! v : Tuple (+1 n), P v) ⇒ R) → π (¬ (`!! w : Tuple n, `!! y : Tuple 1, P (w ⨾ prj 0 y)) ⇒ R)`` | proved | Uses `nested_to_compound` rewrite helper. |
| ALL2 | x, y distinct; H ⊢ ¬(∀(x,y)·P) | H ⊢ ¬(∀x·∀y·P) | ``π (¬ (`!! v, P v)) → π (¬ (`!! w, `!! y, P (w ⨾ prj 0 y)))`` | proved | |
| ALL3 | x, y distinct; H ⊢ (∀(x,y)·P) ⇒ R | H ⊢ (∀x·∀y·P) ⇒ R | ``π ((`!! v, P v) ⇒ R) → π ((`!! w, `!! y, P (w ⨾ prj 0 y)) ⇒ R)`` | proved | |
| ALL4 | x, y distinct; H ⊢ ∀(x,y)·P | H ⊢ ∀x·∀y·P | ``π (`!! v, P v) → π (`!! w, `!! y, P (w ⨾ prj 0 y))`` | proved | |
| ALL5 † | x not free in R; H ⊢ ∀x·(¬P ⇒ R) | H ⊢ ¬(∀x·P) ⇒ R | ``π (`!! v, ¬ (P v) ⇒ R) → π (¬ (`!! v, P v) ⇒ R)`` | proved | |
| ALL6 | H ⊢ (∀x·P) ⇒ FAUX | H ⊢ ¬(∀x·P) | ``π ((`!! v, P v) ⇒ ⊥) → π (¬ (`!! v, P v))`` | proved | HOAS identity (`¬Q ≡ Q ⇒ ⊥`). |
| ALL7 † | x not free in H; (H ⊢ P) ⇝ R; H ⊢ (♢x·R) ⇒ Q | H ⊢ (∀x·P) ⇒ Q | ``(ρ : Π v : Tuple n, Res (P v)) → π ((`♢ v, res_tm (ρ v)) ⇒ Q) → π ((`!! v, P v) ⇒ Q)`` | proved | Result-based form: takes a per-tuple Res chain ρ. Continuation premise uses ♢; conclusion uses `!!`. |
| ALL8 † | x not free in H; H ⊢ P | H ⊢ ∀x·P | ``(Π v : Tuple n, π (P v)) → π (`!! v, P v)`` | proved | `λ f, pi_to_!! _ f`. The emitter introduces a Tuple-n var via `assume v_name` and pushes it into `tuple_binders` for later witness lookup. |
| ALL9 | H, (∀x·T) ⊢ Q | H ⊢ (♡x·T) ⇒ Q | ``(π (`!! v, T v) → π Q) → π ((`♡ v, T v) ⇒ Q)`` | proved | Antecedent transported via `♡_eq_!!`, then `h` applied. |

| Rule | Antecedents | Consequent | Result | LP type | Status | Notes |
|------|-------------|------------|--------|---------|--------|-------|
| ALL7' † | x not free in H; (H ⊢ P) ⇝ R; (H ⊢ (♢x·R) ⇒ Q) ⇝ S | H ⊢ (∀x·P) ⇒ Q | S | ``(ρ : Π v : Tuple n, Res (P v)) → Res ((`♢ v, res_tm (ρ v)) ⇒ Q) → Res ((`!! v, P v) ⇒ Q)`` | proved | `ALL7_1` in `lp/rules/Res.lp`; depends on `!!_cong` and `♢_eq_!!`. |
| ALL8' † | x not free in H; (H ⊢ P) ⇝ Q | H ⊢ ∀x·P | ∀x·Q | ``(ρ : Π v : Tuple n, Res (P v)) → Res (`!! v, P v)`` | proved | `ALL8_1` in `lp/rules/Res.lp`. |
| ALL9' | (H, (∀x·P) ⊢ Q) ⇝ R | H ⊢ (♡x·P) ⇒ Q | (∀x·P) ⇒ R | `Res Q → Res (H ⇒ Q)` | proved | `ALL9_1` in `lp/rules/Res.lp`. |

## A.8 Existential quantification — `lp/rules/Xst.lp`

| Rule | Antecedents | Consequent | LP type | Status | Notes |
|------|-------------|------------|---------|--------|-------|
| XST1 | x, y distinct; H ⊢ ¬(∃(x,y)·P) ⇒ R | H ⊢ ¬(∃x·∃y·P) ⇒ R | ``π (¬ (`?? v, P v) ⇒ R) → π (¬ (`?? w, `?? y, P (w ⨾ prj 0 y)) ⇒ R)`` | proved | Uses `compound_to_nested_∃` / `nested_to_compound_∃`. |
| XST2 | x, y distinct; H ⊢ ¬(∃(x,y)·P) | H ⊢ ¬(∃x·∃y·P) | ``π (¬ (`?? v, P v)) → π (¬ (`?? w, `?? y, P (w ⨾ prj 0 y)))`` | proved | |
| XST3 | x, y distinct; H ⊢ (∃(x,y)·P) ⇒ R | H ⊢ (∃x·∃y·P) ⇒ R | ``π ((`?? v, P v) ⇒ R) → π ((`?? w, `?? y, P (w ⨾ prj 0 y)) ⇒ R)`` | proved | |
| XST4 | x, y distinct; H ⊢ ∃(x,y)·P | H ⊢ ∃x·∃y·P | ``π (`?? v, P v) → π (`?? w, `?? y, P (w ⨾ prj 0 y))`` | proved | |
| XST5 | H ⊢ (∀x·¬P) ⇒ R | H ⊢ ¬(∃x·P) ⇒ R | ``π ((`!! v, ¬ (P v)) ⇒ R) → π (¬ (`?? v, P v) ⇒ R)`` | proved | |
| XST51 | H ⊢ (∀x·P) ⇒ R | H ⊢ ¬(∃x·¬P) ⇒ R | ``π ((`!! v, P v) ⇒ R) → π (¬ (`?? v, ¬ (P v)) ⇒ R)`` | proved | |
| XST6 | H ⊢ ∀x·¬P | H ⊢ ¬(∃x·P) | ``π (`!! v, ¬ (P v)) → π (¬ (`?? v, P v))`` | proved | |
| XST61 | H ⊢ ∀x·P | H ⊢ ¬(∃x·¬P) | ``π (`!! v, P v) → π (¬ (`?? v, ¬ (P v)))`` | proved | |
| XST7 † | x not free in R; H ⊢ ∀x·(P ⇒ R) | H ⊢ (∃x·P) ⇒ R | ``π (`!! v, P v ⇒ R) → π ((`?? v, P v) ⇒ R)`` | proved | |
| XST8 † | x not free in H; (H ⊢ ¬P) ⇝ R; H ⊢ (∀x·R) ⇒ FAUX | H ⊢ ∃x·P | ``(ρ : Π v : Tuple n, Res (¬ (P v))) → π ((`!! v, res_tm (ρ v)) ⇒ ⊥) → π (`?? v, P v)`` | proved | Result-based form via `XST8_1` Res chain in `lp/rules/Res.lp`. The continuation uses `!!` (spec writes ∀, not ♢). |

## A.9 True / False — `lp/rules/TrueFalse.lp`

| Rule | Antecedents | Consequent | LP type | Status | Notes |
|------|-------------|------------|---------|--------|-------|
| VR1 | *(none)* | H ⊢ ¬VRAI ⇒ R | `π (¬ ⊤ ⇒ R)` | proved | |
| VR2 | H ⊢ FAUX | H ⊢ ¬VRAI | `π ⊥ → π (¬ ⊤)` | proved | |
| VR3 | H ⊢ R | H ⊢ VRAI ⇒ R | `π R → π (⊤ ⇒ R)` | proved | |
| VR4 | *(none)* | H ⊢ VRAI | `π ⊤` | proved | |
| FX1 | H ⊢ R | H ⊢ ¬FAUX ⇒ R | `π R → π (¬ ⊥ ⇒ R)` | proved | |
| FX2 | *(none)* | H ⊢ ¬FAUX | `π (¬ ⊥)` | proved | |
| FX3 | *(none)* | H ⊢ FAUX ⇒ R | `π (⊥ ⇒ R)` | proved | |

## A.10 STOP rules — `lp/rules/TrueFalse.lp`

| Rule | Antecedents | Consequent | LP type | Status | Notes |
|------|-------------|------------|---------|--------|-------|
| STOP | P is not FAUX; H ⊢ ¬P ⇒ FAUX | H ⊢ P | `π (¬ P ⇒ ⊥) → π P` | proved | Classical (`¬¬ₑ`). |

| Rule | Antecedents | Consequent | Result | LP type | Status | Notes |
|------|-------------|------------|--------|---------|--------|-------|
| STOP' | *(none)* | H ⊢ P | P | `Res P` | proved | `STOP_1` in `lp/rules/Res.lp` — Res-leaf identity. |

## A.11 INS — `lp/rules/TrueFalse.lp`

| Rule | Antecedents | Consequent | LP type | Status | Notes |
|------|-------------|------------|---------|--------|-------|
| INS | Choose instantiations Q1, …, Qn; H ⊢ Q1 ⇒ (… ⇒ FAUX) | H ⊢ FAUX | `π ⊥ → π P` | proved · emit-trust | LP rule is just `⊥ → P`. The hard part — picking instantiations and bridging arithmetic-match conjuncts — is **trusted** at emit time (see `emit_ins`). |

## A.12 Normalisation — `lp/rules/Nrm.lp`

| Rule | Antecedents | Consequent | LP type | Status | Notes |
|------|-------------|------------|---------|--------|-------|
| NRM1 | x not free in P; H ⊢ P ⇒ S | H ⊢ (♢x·P) ⇒ S | ``π (P ⇒ S) → π ((`♢ _ : Tuple n, P) ⇒ S)`` | proved | Drops the binder via `inh_tuple` witness. |
| NRM2 | x not free in P; H ⊢ (P ⇒ ♢x·Q) ⇒ S | H ⊢ ♢x·(P ⇒ Q) ⇒ S | ``π ((P ⇒ (`♢ v, Q v)) ⇒ S) → π ((`♢ v, P ⇒ Q v) ⇒ S)`` | proved | Bodies use `pi_to_♢` / `♢_to_pi`. |
| NRM3 | x not free in Q; Q is not FAUX; H ⊢ (Q ⇒ S) ∧ ((∀x·¬P) ⇒ S) | H ⊢ ♢x·(P ⇒ Q) ⇒ S | ``π ((Q ⇒ S) ∧ ((`!! v, ¬ (P v)) ⇒ S)) → π ((`♢ v, P v ⇒ Q) ⇒ S)`` | proved | Classical (em on `?? v, P v`). Premise's `∀x` stays `!!`. |
| NRM4 | x not free in Q; H ⊢ (Q ⇒ ♢x·(P ⇒ R)) ⇒ S | H ⊢ ♢x·(P ⇒ (Q ⇒ R)) ⇒ S | ``π ((Q ⇒ (`♢ v, P v ⇒ R v)) ⇒ S) → π ((`♢ v, P v ⇒ Q ⇒ R v) ⇒ S)`` | proved | |
| NRM5 | H ⊢ ♢x·(P ∧ Q ⇒ R) ⇒ S | H ⊢ ♢x·(P ⇒ (Q ⇒ R)) ⇒ S | ``π ((`♢ v, (P v ∧ Q v) ⇒ R v) ⇒ S) → π ((`♢ v, P v ⇒ Q v ⇒ R v) ⇒ S)`` | proved | |
| NRM6 | H ⊢ ♢x·(R ⇒ P) ⇒ (♢x·(R ⇒ Q) ⇒ S) | H ⊢ ♢x·(R ⇒ P ∧ Q) ⇒ S | ``π ((`♢ v, R v ⇒ P v) ⇒ ((`♢ v, R v ⇒ Q v) ⇒ S)) → π ((`♢ v, R v ⇒ (P v ∧ Q v)) ⇒ S)`` | proved | |
| NRM7 | H ⊢ (♢x·P) ⇒ ((♢x·Q) ⇒ S) | H ⊢ ♢x·(P ∧ Q) ⇒ S | ``π ((`♢ v, P v) ⇒ ((`♢ v, Q v) ⇒ S)) → π ((`♢ v, P v ∧ Q v) ⇒ S)`` | proved | |
| NRM8 † | x, y distinct; H ⊢ (♢(x,y)·Q) ⇒ S | H ⊢ (♢x·∀y·Q) ⇒ S | ``π ((`♢ v : Tuple (n ++ m), Q (take v) (drop v)) ⇒ S) → π ((`♢ x : Tuple n, `!! y : Tuple m, Q x y) ⇒ S)`` | proved | Via the `take` / `drop` split (`Quant.lp`). HO pattern `Q x y` lets Lambdapi infer Q automatically. |
| NRM9 † | x, y distinct; y not free in P; H ⊢ ♢(x,y)·(P ⇒ Q) ⇒ S | H ⊢ ♢x·(P ⇒ ∀y·Q) ⇒ S | ``π ((`♢ v : Tuple (n ++ m), P (take v) ⇒ Q (take v) (drop v)) ⇒ S) → π ((`♢ x : Tuple n, P x ⇒ (`!! y : Tuple m, Q x y)) ⇒ S)`` | proved | Same `take` / `drop` machinery as NRM8. |
| NRM10 | H ⊢ ♡x·¬(P ∧ Q) ⇒ R | H ⊢ ♢x·(P ∧ Q ⇒ FAUX) ⇒ R | ``π ((`♡ v, ¬ (P v ∧ Q v)) ⇒ R) → π ((`♢ v, (P v ∧ Q v) ⇒ ⊥) ⇒ R)`` | proved | ♡ on premise, ♢ on conclusion. |
| NRM11 | H ⊢ ♡x·¬(VRAI ∧ P) ⇒ R | H ⊢ ♢x·(P ⇒ FAUX) ⇒ R | ``π ((`♡ v, ¬ (⊤ ∧ P v)) ⇒ R) → π ((`♢ v, P v ⇒ ⊥) ⇒ R)`` | proved | |
| NRM12 | H ⊢ ♡x·¬(P ∧ Q) ⇒ R | H ⊢ ♢x·(P ⇒ ¬Q) ⇒ R | ``π ((`♡ v, ¬ (P v ∧ Q v)) ⇒ R) → π ((`♢ v, P v ⇒ ¬ (Q v)) ⇒ R)`` | proved | |
| NRM13 | H ⊢ ♡x·¬(P ∧ ¬Q) ⇒ R | H ⊢ ♢x·(P ⇒ Q) ⇒ R | ``π ((`♡ v, ¬ (P v ∧ ¬ (Q v))) ⇒ R) → π ((`♢ v, P v ⇒ Q v) ⇒ R)`` | proved | |
| NRM14 | H ⊢ ♡x·¬(VRAI ∧ P) ⇒ R | H ⊢ (♢x·¬P) ⇒ R | ``π ((`♡ v, ¬ (⊤ ∧ P v)) ⇒ R) → π ((`♢ v, ¬ (P v)) ⇒ R)`` | proved | |
| NRM15 | H ⊢ ♡x·¬(VRAI ∧ ¬P) ⇒ R | H ⊢ (♢x·P) ⇒ R | ``π ((`♡ v, ¬ (⊤ ∧ ¬ (P v))) ⇒ R) → π ((`♢ v, P v) ⇒ R)`` | proved | |
| NRM16 | ∀x·P in H; Q | H ⊢ (♡x·P) ⇒ Q | ``π (`!! v, P v) → π Q → π ((`♡ v, P v) ⇒ Q)`` | proved | Trivial — body absorbs the antecedent. |
| NRM17 | ∀x·¬(VRAI ∧ P) in H; ∃E with [x := E] P = R | H ⊢ ♡y·¬(VRAI ∧ ¬R) ⇒ Q | ``π (`!! v, P v) → π Q → π ((`♡ v, P v) ⇒ Q)`` | proved | Collapses to NRM16 shape at LP. |
| NRM18 | ∀x·¬(VRAI ∧ ¬P) in H; ∃E with [x := E] P = R | H ⊢ ♡y·¬(VRAI ∧ R) ⇒ Q | ``(v : Tuple n) → π (`!! u, ¬ (⊤ ∧ ¬ (P u))) → π (P v = R) → π ((`♡ _ : Tuple n, ¬ (⊤ ∧ R)) ⇒ Q)`` | proved | |
| NRM19 | P in H; ∃E with [x := E] R = P | H ⊢ ♡x·¬(VRAI ∧ R) ⇒ Q | ``(v : Tuple n) → π (R v) → π ((`♡ u, ¬ (⊤ ∧ R u)) ⇒ Q)`` | proved | Emitter pulls the witness from `tuple_binders`. |
| NRM20 | x not free in E; H ⊢ ♡y·¬[x := E] P ⇒ Q | H ⊢ ♡(x,y)·¬(x = E ∧ P) ⇒ Q | ``[ps : Tuple (+1 n) → 𝕃* o] (E : τ ι) → (Π v, π (popl (ps v) = (prj 0 v = E))) → π ((`♡ y : Tuple n, ¬ ⋀ dropl (ps (y ⨾ E))) ⇒ Q) → π ((`♡ v : Tuple (+1 n), ¬ ⋀ (ps v)) ⇒ Q)`` | proved · emitted | `ps` is the *full* conjunct list, inferred by unification from the goal; the leading `x = E` is its head (`popl`), the body its tail (`dropl`). `dynamic:nrm20` supplies E (env-rendered) and the `eq_refl` head-equality witness; `⋀_pop_intro` rebuilds `⋀ (ps v)`. |
| NRM21 | x not free in E; H ⊢ ♡y·¬[x := E] P ⇒ Q | H ⊢ ♡(x,y)·¬(P ∧ E = x) ⇒ Q | ``(E : τ ι) → π ((`♡ y : Tuple n, ¬ (P (y ⨾ E))) ⇒ Q) → π ((`♡ v : Tuple (+1 n), ¬ (P v ∧ (E = prj 0 v))) ⇒ Q)`` | proved · partial-emit | Unsupported until a concrete trace shape is implemented. |
| NRM22 | H ⊢ ¬⊤ ⇒ Q | H ⊢ ♡x·¬(⊤ ∧ x = E) ⇒ Q | ``(E : τ ι) → π (¬ ⊤ ⇒ Q) → π ((`♡ v : Tuple 1, ¬ ⋀ (∎ ∷ ⊤ ∷ (prj 0 v = E))) ⇒ Q)`` | proved · emitted | Replay shape (from `subset_singleton`/`subset_literal2`) is a *literal* ⊤ head fed by NRM14 — not the spec's abstract `P`, which only stranded a `?P (prj 0 v) ≡ ⊤` HO-unification. `dynamic:nrm22` supplies E (env-rendered); the child is VR1. |
| NRM23 | x not free in E; H ⊢ ¬[x := E] P ⇒ Q | H ⊢ ♡x·¬(P ∧ E = x) ⇒ Q | ``(E : τ ι) → π (¬ (P E) ⇒ Q) → π ((`♡ v : Tuple 1, ¬ (P (prj 0 v) ∧ (E = prj 0 v))) ⇒ Q)`` | proved · partial-emit | Unsupported until a concrete trace shape is implemented. |
| NRM24 | P is not of form A ∧ B; H ⊢ ♡x·¬(VRAI ∧ P) ⇒ Q | H ⊢ ♡x·¬P ⇒ Q | ``π ((`♡ v, ¬ (⊤ ∧ P v)) ⇒ Q) → π ((`♡ v, ¬ (P v)) ⇒ Q)`` | proved | |
| NRM25 | x not free in P; H ⊢ P | H ⊢ forall2(x)·P | ``π P → π (`♡ _ : Tuple n, P)`` | proved | `pi_to_♡` over a constant body. |
| NRM26 | y not free in P; H ⊢ forall2(x,…)·P | H ⊢ forall2(x,y,…)·P | ``π (`♡ v, P v) → π (`♡ v : Tuple (+1 n), P (nrm26_drop_last v))`` | proved | Transports input via `♡_eq_!!` and uses `nrm26_drop_proof`. |
| NRM27 | (xi ≤ 0) and (−xi ≤ 0) in (P ∧ ··· ∧ Q); R = [xi := 0]…; H ⊢ ♢(x1,…,xi−1,xi+1,…,xn)·¬R | H ⊢ ♡(x1,…,xn)·¬(P ∧ ··· ∧ Q) | — | not-impl | Arithmetic solver dispatch; no LP rule yet. |
| NRM28 | (x ≤ 0) and (−x ≤ 0) in (P ∧ ··· ∧ Q); S = [x := 0]…; H ⊢ ¬(S) ⇒ R | H ⊢ (♡(x)·¬(P ∧ ··· ∧ Q)) ⇒ R | — | not-impl | |
| NRM29 | (a + xi ≤ 0) and (b − xi ≤ 0) in (P ∧ ··· ∧ Q); solver(a + b) = 0; S = [xi := b]…; H ⊢ ♢·¬S ⇒ R | H ⊢ (♡(x1,…,xn)·¬(P ∧ ··· ∧ Q)) ⇒ R | — | not-impl | |
| NRM29_1 | (xi + a ≤ 0) and (−xi + b ≤ 0) in (P ∧ ··· ∧ Q); solver(a + b) = 0; … | (same) | — | not-impl | |
| NRM30 | (a + x ≤ 0) and (b − x ≤ 0) in (P ∧ ··· ∧ Q); solver(a + b) = 0; S = [x := b]…; H ⊢ ¬S ⇒ R | H ⊢ (♡x·¬(P ∧ ··· ∧ Q)) ⇒ R | — | not-impl | |
| NRM30_1 | (x + a ≤ 0) and (−x + b ≤ 0) in (P ∧ ··· ∧ Q); … | (same) | — | not-impl | |

## A.13 Equality rules — `lp/rules/Eq.lp`

| Rule | Antecedents | Consequent | LP type | Status | Notes |
|------|-------------|------------|---------|--------|-------|
| EVR1 | *(none)* | H ⊢ ¬(E = E) ⇒ P | `π (¬ (E = E) ⇒ P)` | proved | |
| EVR11 | n ∈ ℕ; m ∈ ℕ; n ≠ m | H ⊢ (n = m) ⇒ P | `π (n ϵ NAT) → π (m ϵ NAT) → π (n ≠ m) → π ((n = m) ⇒ P)` | proved | |
| EVR2 | H ⊢ FAUX | H ⊢ ¬(E = E) | `π ⊥ → π (¬ (E = E))` | proved | |
| EVR3 | H ⊢ P | H ⊢ (E = E) ⇒ P | `π P → π ((E = E) ⇒ P)` | proved | |
| EVR4 | *(none)* | H ⊢ (E = E) | `π (E = E)` | proved | |
| EAXM1 | ¬(F = E) in H | H ⊢ (E = F) ⇒ P | `π (¬ (F = E)) → π ((E = F) ⇒ P)` | proved | Hyp lookup. |
| EAXM2 | (F = E) in H | H ⊢ ¬(E = F) ⇒ P | `π (F = E) → π (¬ (E = F) ⇒ P)` | proved | Hyp lookup. |
| EAXM31 | (F = E) in H | H ⊢ (E = F) | `π (F = E) → π (E = F)` | proved | |
| EAXM32 | ¬(F = E) in H | H ⊢ ¬(E = F) | `π (¬ (F = E)) → π (¬ (E = F))` | proved | |
| EIMP51 | ¬(F = E) in H; H ⊢ P | H ⊢ ¬(E = F) ⇒ P | `π (¬ (F = E)) → π P → π (¬ (E = F) ⇒ P)` | proved | |
| EIMP52 | (F = E) in H; H ⊢ P | H ⊢ (E = F) ⇒ P | `π (F = E) → π P → π ((E = F) ⇒ P)` | proved | |
| EQC1 | H ⊢ ¬(a = c) ∨ ¬(b = d) ⇒ P | H ⊢ ¬((a,b) = (c,d)) ⇒ P | `π ((¬ (a = c) ∨ ¬ (b = d)) ⇒ P) → π (¬ ((a ↦ b) = (c ↦ d)) ⇒ P)` | proved | Pair `↦`. |
| EQC2 | H ⊢ (a = c) ∧ (b = d) ⇒ P | H ⊢ ((a,b) = (c,d)) ⇒ P | `π (((a = c) ∧ (b = d)) ⇒ P) → π (((a ↦ b) = (c ↦ d)) ⇒ P)` | proved | |
| EQS1 | H ⊢ E = F ⇒ R | H ⊢ eql_set(E,F) ⇒ R | `π ((E = F) ⇒ R) → π (eql_set E F ⇒ R)` | proved | |
| EQS2 | H ⊢ FAUX ⇒ R | H ⊢ ¬eql_set(E,F) ⇒ R | `π (¬ (E = F) ⇒ R) → π (¬ eql_set E F ⇒ R)` | proved | Spec writes `H ⊢ FAUX ⇒ R` for the antecedent; the LP form takes `¬ (E = F) ⇒ R` (semantically equivalent given the hypothesis). |
| EAXM91 | ∀x·¬(VRAI ∧ p = q) in H; ∃E with [x := E](q = p) = (a = b) | H ⊢ (a = b) ⇒ Q | ``(v : Tuple n) → π (`!! u, ¬ (⊤ ∧ (p u = q u))) → π ((q v = p v) ⇒ Q)`` | proved | Tuple-uniform; witness as for AXM9. |
| EAXM92 | ∀x·¬(VRAI ∧ ¬(p = q)) in H; ∃E with [x := E](q = p) = (a = b) | H ⊢ ¬(a = b) ⇒ Q | ``(v : Tuple n) → π (`!! u, ¬ (⊤ ∧ ¬ (p u = q u))) → π (¬ (q v = p v) ⇒ Q)`` | proved | |
| OPR1 | x is a variable; x not free in H, E; Q = [x := E] P; H ⊢ Q | H ⊢ (x = E) ⇒ P | `π (P E) → π ((x = E) ⇒ P x)` | proved | `rewrite heq`. **Primed-form note:** PP's actual `OPR1_1` does *not* follow the §8.13 Schema 1 derivation: Schema 1 would propagate the antecedent's result, dropping the `(x = E) ⇒` wrapper in the consequent. PP's chain step instead **keeps the wrapper** and only substitutes inside the body — i.e. `Res (x = E ⇒ P E) → Res (x = E ⇒ P x)` (see e.g. `bench/prv/subset_001.replay:19–20`). Reflected in `opr1_eq : π ((x = E ⇒ P x) = (x = E ⇒ P E))` (provable by case-split on `x = E` inside `propExt`); the genuine Schema 1 lift `Res (P E) → Res ((x = E) ⇒ P x)` is *not* propositionally available without a hypothesis `heq`. |
| OPR2 | (mirror of OPR1, equality reversed) | H ⊢ (E = x) ⇒ P | `π (P E) → π ((E = x) ⇒ P x)` | proved | Same primed-form divergence as OPR1: `OPR2_1` keeps `(E = x) ⇒` on both sides; `opr2_eq` proves the wrapper-preserving equality. |
| ECTR1 | ¬Q in H; replacing E by F in Q gives R; R in H | H ⊢ (E = F) ⇒ P | `π (¬ (Q E)) → π (Q F) → π ((E = F) ⇒ P)` | proved | |
| ECTR2 | (mirror) | H ⊢ (F = E) ⇒ P | `π (¬ (Q E)) → π (Q F) → π ((F = E) ⇒ P)` | proved | |
| ECTR3 | E = F in H; replacing E by F in P gives R; R in H | H ⊢ ¬P ⇒ Q | `π (E = F) → π (P F) → π (¬ (P E) ⇒ Q)` | proved | |
| ECTR4 | (mirror) | H ⊢ ¬P ⇒ Q | `π (F = E) → π (P F) → π (¬ (P E) ⇒ Q)` | proved | |
| ECTR5 | E = F in H; replacing E by F in P gives R; ¬R in H | H ⊢ P ⇒ Q | `π (E = F) → π (¬ (P F)) → π ((P E) ⇒ Q)` | proved | |
| ECTR6 | (mirror) | H ⊢ P ⇒ Q | `π (F = E) → π (¬ (P F)) → π ((P E) ⇒ Q)` | proved | |

## A.14 Arithmetic rules — `lp/rules/Arith.lp`

| Rule | Antecedents | Consequent | LP type | Status | Notes |
|------|-------------|------------|---------|--------|-------|
| AR1 | H ⊢ R | H ⊢ E ≤ E ⇒ R | `π R → π ((E ≤ E) ⇒ R)` | proved | Uses `B.lp`'s `leq_refl`. |
| AR2 | a, b numeric; a > b | H ⊢ a ≤ b ⇒ R | `π (a > b) → π ((a ≤ b) ⇒ R)` | proved · emit-trust | Emitter passes the `a > b` proof as `trust`. |
| AR3 | H ⊢ 1 − a ≤ 0 ⇒ R | H ⊢ ¬(a ≤ 0) ⇒ R | `(a : τ ι) → π ((𝟏 - a ≤ 𝟎) ⇒ R) → π (¬ (a ≤ 𝟎) ⇒ R)` | proved · emit-trust | `AR3_F` (phantom) and `AR3'` (bridged variant) cover solver-normalised shapes; unknown equality bridges are passed as trusted side-conditions. |
| AR4 | F ≤ 0 in H; E + F > 0 | H ⊢ E ≤ 0 ⇒ R | `(F : τ ι) → π (F ≤ 𝟎) → π ((E + F) > 𝟎) → π ((E ≤ 𝟎) ⇒ R)` | proved · emit-trust | Emitter resolves `F` from a hypothesis and passes the numeric side-condition as `trust`. |
| AR5 | a ≪ 0 in H; H ⊢ a = 0 ⇒ (−a ≤ 0 ⇒ R) | H ⊢ −a ≤ 0 ⇒ R | `π (a ≪ 𝟎) → π ((— a ≤ 𝟎) ⇒ ((a = 𝟎) ⇒ R)) → π ((— a ≤ 𝟎) ⇒ R)` | proved · emit-trust | Antecedent order commuted vs. spec; emitter passes the solver side-condition as `trust`. |
| AR6 | −a ≪ 0 in H; H ⊢ a = 0 ⇒ (a ≤ 0 ⇒ R) | H ⊢ a ≤ 0 ⇒ R | `π ((— a) ≤ 𝟎) → π ((a ≤ 𝟎) ⇒ ((a = 𝟎) ⇒ R)) → π ((a ≤ 𝟎) ⇒ R)` | proved · emit-trust | Emitter passes the solver side-condition as `trust`. |
| AR7 | c + b ≪ 0 in H; a + c = 0; H ⊢ a = b ⇒ (a − b ≤ 0 ⇒ R) | H ⊢ a − b ≤ 0 ⇒ R | `(c : τ ι) → π ((c + b) ≪ 𝟎) → π ((a + c) = 𝟎) → π ((a = b) ⇒ (((a - b) ≤ 𝟎) ⇒ R)) → π (((a - b) ≤ 𝟎) ⇒ R)` | proved · emit-trust | Emitter passes solver side-conditions as `trust`. |
| AR8 | a − b ≪ 0 in H; a + c = 0; H ⊢ a = b ⇒ (c + b ≤ 0 ⇒ R) | H ⊢ c + b ≤ 0 ⇒ R | `(a : τ ι) → π ((a - b) ≪ 𝟎) → π ((a + c) = 𝟎) → π ((a = b) ⇒ (((c + b) ≤ 𝟎) ⇒ R)) → π (((c + b) ≤ 𝟎) ⇒ R)` | proved · emit-trust | Emitter computes the witness `a` from a child equality and passes solver side-conditions as `trust`. |
| AR9 | solver(E) = F; H ⊢ F ≤ 0 ⇒ R | H ⊢ E ≤ 0 ⇒ R | `(F : τ ι) → π (E = F) → π ((F ≤ 𝟎) ⇒ R) → π ((E ≤ 𝟎) ⇒ R)` | proved · emit-trust | Emitter passes the equality as a trusted side-condition (`emit_args:dynamic:ar9`). |
| AR10 | solver(P) = Q; H ⊢ Q ⇒ R | H ⊢ P ⇒ R | `π (P = Q) → π (Q ⇒ R) → π (P ⇒ R)` | phantom | LP rule defined for completeness — PP emits AR10 only when Q = P (solver no-op), so the LP rule is never applied. |
| AR11 | *(none)* | H ⊢ ¬(x ≤ x) ⇒ P | `π (¬ (E ≤ E) ⇒ P)` | proved | |
| AR12 | H, (a ≤ b) ⊢ P | H ⊢ (a ≪ b) ⇒ P | `(π (a ≤ b) → π P) → π ((a ≤ b) ⇒ P)` | proved | HOAS-introduces the antecedent. |

*Implementation extras (not in spec):*

| Rule | LP type | Status | Notes |
|------|---------|--------|-------|
| AR3' | `(a r : τ ι) → π (𝟏 - a = r) → π ((r ≤ 𝟎) ⇒ R) → π (¬ (a ≤ 𝟎) ⇒ R)` | proved | Bridged variant for solver-normalised AR3 sub-premises. |
| AR3_F | (HOAS identity) | phantom | Emit-side variant; `hoas_identity:true`. |
| AR13 | `π ((𝟏 - a) = b) → π (b ≤ 𝟎) → π (¬ (a ≤ 𝟎))` | proved · emit-trust | Solver-confirmed contradiction; emitter passes both args as `trust`. |

## A.15 Boolean rules — `lp/rules/Bool.lp`

| Rule | Antecedents | Consequent | LP type | Status | Notes |
|------|-------------|------------|---------|--------|-------|
| BOOL11 | H, (v = TRUE), ¬(v = FALSE) ⊢ P | H ⊢ (v = TRUE) ⇒ P | `(π (V = BTRUE) → π (¬ (V = BFALSE)) → π P) → π ((V = BTRUE) ⇒ P)` | proved | |
| BOOL12 | H, (v = FALSE), ¬(v = TRUE) ⊢ P | H ⊢ (v = FALSE) ⇒ P | `(π (V = BFALSE) → π (¬ (V = BTRUE)) → π P) → π ((V = BFALSE) ⇒ P)` | proved | |
| BOOL21 | H ⊢ (v = TRUE) ⇒ P | H ⊢ (TRUE = v) ⇒ P | `π ((V = BTRUE) ⇒ P) → π ((BTRUE = V) ⇒ P)` | proved | |
| BOOL22 | H ⊢ (v = FALSE) ⇒ P | H ⊢ (FALSE = v) ⇒ P | `π ((V = BFALSE) ⇒ P) → π ((BFALSE = V) ⇒ P)` | proved | |
| BOOL31 | H ⊢ (v = FALSE) ⇒ P | H ⊢ ¬(v = TRUE) ⇒ P | `(hb : π (V ϵ BOOL)) → π ((V = BFALSE) ⇒ P) → π (¬ (V = BTRUE) ⇒ P)` | proved · emit-trust | Emitter passes the `V ϵ BOOL` proof as `trust` (PP can't reason about `v : BOOL` abstractly). |
| BOOL32 | H ⊢ (v = TRUE) ⇒ P | H ⊢ ¬(v = FALSE) ⇒ P | `(hb : π (V ϵ BOOL)) → π ((V = BTRUE) ⇒ P) → π (¬ (V = BFALSE) ⇒ P)` | proved · emit-trust | As BOOL31. |
| BOOL41 | H ⊢ (v = FALSE) ⇒ P | H ⊢ ¬(TRUE = v) ⇒ P | `(hb : π (v ϵ BOOL)) → π ((v = BFALSE) ⇒ P) → π (¬ (BTRUE = v) ⇒ P)` | proved · emit-trust | As BOOL31. |
| BOOL42 | H ⊢ (v = TRUE) ⇒ P | H ⊢ ¬(FALSE = v) ⇒ P | `(hb : π (v ϵ BOOL)) → π ((v = BTRUE) ⇒ P) → π (¬ (BFALSE = v) ⇒ P)` | proved · emit-trust | As BOOL31. |
| BOOL51 | *(none)* | H ⊢ (TRUE = FALSE) ⇒ P | `π ((BTRUE = BFALSE) ⇒ P)` | proved | |
| BOOL52 | *(none)* | H ⊢ ¬(FALSE = TRUE) ⇒ P | `π ((BFALSE = BTRUE) ⇒ P)` | proved | |
