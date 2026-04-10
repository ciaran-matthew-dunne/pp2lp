## Appendix A: Summary of Rules Used

### A.1 Conjunction

| Rule | Antecedents | Consequent | Notes |
|------|-------------|------------|-------|
| AND1 | H ⊢ ¬Q ⇒ R; H ⊢ ¬P ⇒ R | H ⊢ ¬(P ∧ Q) ⇒ R | Proved |
| AND2 | H ⊢ P ⇒ ¬Q | H ⊢ ¬(P ∧ Q) | Proved |
| AND3 | H ⊢ P ⇒ (Q ⇒ R) | H ⊢ (P ∧ Q) ⇒ R | Proved |
| AND4 | H ⊢ Q; H ⊢ P | H ⊢ P ∧ Q | Proved |
| AND5 | P ∧ ··· contains A; H ⊢ P ∧ ··· ∧ B ∧ ··· ⇒ R | H ⊢ P ∧ ··· ∧ (A ⇒ B) ∧ ··· ⇒ R | Proved; LP uses forward function `(π C → π C') → π (C' ⇒ R) → π (C ⇒ R)` — emitter generates ∧ₑ/∧ᵢ lambdas |

### A.2 Disjunctions

| Rule | Antecedents | Consequent | Notes |
|------|-------------|------------|-------|
| OR1 | H ⊢ ¬P ⇒ (¬Q ⇒ R) | H ⊢ ¬(P ∨ Q) ⇒ R | Proved |
| OR2 | H ⊢ ¬Q; H ⊢ ¬P | H ⊢ ¬(P ∨ Q) | Proved |
| OR3 | H ⊢ Q ⇒ R; H ⊢ P ⇒ R | H ⊢ (P ∨ Q) ⇒ R | Proved |
| OR4 | H ⊢ ¬P ⇒ Q | H ⊢ P ∨ Q | Proved |

### A.3 Implications

| Rule | Antecedents | Consequent | Notes |
|------|-------------|------------|-------|
| IMP1 | H ⊢ P ⇒ (¬Q ⇒ R) | H ⊢ ¬(P ⇒ Q) ⇒ R | Proved |
| IMP2 | H ⊢ ¬Q; H ⊢ P | H ⊢ ¬(P ⇒ Q) | Proved |
| IMP3 | H ⊢ Q ⇒ R; H ⊢ ¬P ⇒ R | H ⊢ (P ⇒ Q) ⇒ R | Proved |
| IMP4 | H, P ⊢ Q | H ⊢ P ⇒ Q | Proved; HOAS: `(π P → π Q) → π (P ⇒ Q)` |
| IMP5 | P is in H; H ⊢ Q | H ⊢ P ⇒ Q | Proved; LP type `π Q → π (P ⇒ Q)` — P-in-H is a side condition |

| Rule | Antecedents | Consequent | Result | Notes |
|------|-------------|------------|--------|-------|
| IMP4′ | (H, P ⊢ Q) ⇝ R | H ⊢ P ⇒ Q | P ⇒ R | `imp4_r` in Res.lp; `result (imp4_r h) ↪ P ⇒ result h` |

### A.4 Equivalence

| Rule | Antecedents | Consequent | Notes |
|------|-------------|------------|-------|
| EQV1 | H ⊢ P ⇒ (¬Q ⇒ R); H ⊢ ¬P ⇒ (Q ⇒ R) | H ⊢ ¬(P ⇔ Q) ⇒ R | Proved |
| EQV2 | H ⊢ P ⇒ ¬Q; H ⊢ ¬Q ⇒ P | H ⊢ ¬(P ⇔ Q) | Proved |
| EQV3 | H ⊢ P ⇒ (Q ⇒ R); H ⊢ ¬P ⇒ (¬Q ⇒ R) | H ⊢ (P ⇔ Q) ⇒ R | Proved |
| EQV4 | H ⊢ P ⇒ Q; H ⊢ Q ⇒ P | H ⊢ P ⇔ Q | Proved |

### A.5 Negations

| Rule | Antecedents | Consequent | Notes |
|------|-------------|------------|-------|
| NOT1 | H ⊢ P ⇒ R | H ⊢ ¬¬P ⇒ R | Proved |
| NOT2 | H ⊢ P | H ⊢ ¬¬P | Proved |

### A.6 Axioms

| Rule | Antecedents | Consequent | Notes |
|------|-------------|------------|-------|
| AXM1 | ¬P is in H | H ⊢ P ⇒ Q | Proved; LP takes `π (¬P)` as explicit premise |
| AXM2 | P is in H | H ⊢ ¬P ⇒ Q | Proved; LP takes `π P` as explicit premise |
| AXM3 | P is in H | H ⊢ P | Proved; identity |
| AXM4 | R is in H | H ⊢ P ⇒ R | Proved; LP takes `π R` as explicit premise |
| AXM5 | ¬Q is in H | H ⊢ P ⇒ (Q ⇒ R) | Proved; LP takes `π (¬Q)` as explicit premise |
| AXM6 | Q is in H | H ⊢ P ⇒ (¬Q ⇒ R) | Proved; LP takes `π Q` as explicit premise |
| AXM7 | | H ⊢ P ⇒ P | Proved |
| AXM8 | P ∧ ··· contains R | H ⊢ P ∧ ··· ⇒ R | Proved; LP uses forward function like AND5 — emitter generates ∧ₑ/∧ᵢ lambdas |
| AXM9 | ∀x · ¬(TRUE ∧ P) is in H; there exists E such that [x := E] P = R | H ⊢ R ⇒ Q | Proved; HOAS: takes `π (∀x, ¬(⊤ ∧ P x))` + witness `E`; also has AXM9_2 for 2 variables |

### A.7 Universal Quantifications

| Rule | Antecedents | Consequent | Notes |
|------|-------------|------------|-------|
| ALL1 | x and y are distinct; H ⊢ ¬(∀(x, y) · P) ⇒ R | H ⊢ ¬(∀x · ∀y · P) ⇒ R | Proved; **identity in HOAS** — ∀(x,y) = ∀x·∀y by currying |
| ALL2 | x and y are distinct; H ⊢ ¬(∀(x, y) · P) | H ⊢ ¬(∀x · ∀y · P) | Proved; **identity in HOAS** |
| ALL3 | x and y are distinct; H ⊢ (∀(x, y) · P) ⇒ R | H ⊢ (∀x · ∀y · P) ⇒ R | Proved; **identity in HOAS** |
| ALL4 | x and y are distinct; H ⊢ ∀(x, y) · P | H ⊢ ∀x · ∀y · P | Proved; **identity in HOAS** |
| ALL5 | x not free in R; H ⊢ ∀x · (¬P ⇒ R) | H ⊢ ¬(∀x · P) ⇒ R | Proved |
| ALL5 | x is free in R; y not free in P, R; S = [x := y] P; H ⊢ ∀y · (¬S ⇒ R) | H ⊢ ¬(∀x · P) ⇒ R | **HOAS**: α-equivalence automatic — same LP rule handles both variants |
| ALL6 | H ⊢ (∀x · P) ⇒ FALSE | H ⊢ ¬(∀x · P) | Proved; definitional (¬Q ≡ Q ⇒ ⊥) |
| ALL7 | x not free in H; (H ⊢ P) ⇝ R; H ⊢ (♢x · R) ⇒ Q | H ⊢ (∀x · P) ⇒ Q | Proved; branching rule with normalisation chain |
| ALL7 | x is free in H; y not free in A, H; P = [x := y] A; (H ⊢ P) ⇝ R; H ⊢ (♢x · R) ⇒ Q | H ⊢ (∀x · A) ⇒ Q | **HOAS**: α-equivalence — same LP rule handles both |
| ALL8 | x not free in H; H ⊢ P | H ⊢ ∀x · P | Proved; **identity in HOAS** — emitter uses `assume` |
| ALL8 | x is free in H; y not free in P, H; R = [x := y] P; H ⊢ R | H ⊢ ∀x · P | **HOAS**: α-equivalence — same LP rule handles both |
| ALL9 | H, (∀x · T) ⊢ Q | H ⊢ (♡x · T) ⇒ Q | Proved; HOAS: `(π (∀x, T x) → π Q) → π ((♡x, T x) ⇒ Q)` |

| Rule | Antecedents | Consequent | Result | Notes |
|------|-------------|------------|--------|-------|
| ALL7′ | x not free in H; (H ⊢ P) ⇝ R; (H ⊢ (♢x · R) ⇒ Q) ⇝ S | H ⊢ (∀x · P) ⇒ Q | S | `ALL7r` in Res.lp; also ALL7_2r for 2 variables |
| ALL7′ | x is free in H; ... | H ⊢ (∀x · A) ⇒ Q | S | **HOAS**: same rule handles both |
| ALL8′ | x not free in H; (H ⊢ P) ⇝ Q | H ⊢ ∀x · P | ∀x · Q | `all8_r` in Res.lp; `result (all8_r f) ↪ ∀x, result (f x)` |
| ALL8′ | x is free in H; ... | H ⊢ ∀x · P | ∀y · Q | **HOAS**: same rule handles both |
| ALL9′ | (H, (∀x · P) ⊢ Q) ⇝ R | H ⊢ (♡x · P) ⇒ Q | (∀x · P) ⇒ R | `all9_r` in Res.lp; `result (all9_r h) ↪ H ⇒ result h` |

### A.8 Existential Quantification

| Rule | Antecedents | Consequent | Notes |
|------|-------------|------------|-------|
| XST1 | x and y are distinct; H ⊢ ¬(∃(x, y) · P) ⇒ R | H ⊢ ¬(∃x · ∃y · P) ⇒ R | Proved; **identity in HOAS** |
| XST2 | x and y are distinct; H ⊢ ¬(∃(x, y) · P) | H ⊢ ¬(∃x · ∃y · P) | Proved; **identity in HOAS** |
| XST3 | x and y are distinct; H ⊢ (∃(x, y) · P) ⇒ R | H ⊢ (∃x · ∃y · P) ⇒ R | Proved; **identity in HOAS** |
| XST4 | x and y are distinct; H ⊢ ∃(x, y) · P | H ⊢ ∃x · ∃y · P | Proved; **identity in HOAS** |
| XST5 | H ⊢ (∀x · ¬P) ⇒ R | H ⊢ ¬(∃x · P) ⇒ R | Proved; also XST5_2 for 2 variables |
| XST51 | H ⊢ (∀x · P) ⇒ R | H ⊢ ¬(∃x · ¬P) ⇒ R | Proved |
| XST6 | H ⊢ ∀x · ¬P | H ⊢ ¬(∃x · P) | Proved; also XST6_2 for 2 variables |
| XST61 | H ⊢ ∀x · P | H ⊢ ¬(∃x · ¬P) | Proved |
| XST7 | x not free in R; H ⊢ ∀x · (P ⇒ R) | H ⊢ (∃x · P) ⇒ R | Proved; also XST7_2 for 2 variables |
| XST7 | x is free in R; y not free in P, R; Q = [x := y] P; H ⊢ ∀y · (Q ⇒ R) | H ⊢ (∃x · P) ⇒ R | **HOAS**: α-equivalence — same LP rule handles both |
| XST8 | x not free in H; (H ⊢ ¬P) ⇝ R; H ⊢ (∀x · R) ⇒ FALSE | H ⊢ ∃x · P | Proved; branching with ¬¬-elimination; also XST8_2 for 2 vars |
| XST8 | x is free in H; ... | H ⊢ (∃x · A) | **HOAS**: same rule handles both; `XST8r`/`XST8_2r` in Res.lp |

### A.9 True and False

| Rule | Antecedents | Consequent | Notes |
|------|-------------|------------|-------|
| VR1 | | H ⊢ ¬TRUE ⇒ R | Proved |
| VR2 | H ⊢ FALSE | H ⊢ ¬TRUE | Proved |
| VR3 | H ⊢ R | H ⊢ TRUE ⇒ R | Proved |
| VR4 | | H ⊢ TRUE | Proved |
| FX1 | H ⊢ R | H ⊢ ¬FALSE ⇒ R | Proved |
| FX2 | | H ⊢ ¬FALSE | Proved |
| FX3 | | H ⊢ FALSE ⇒ R | Proved |

### A.10 STOP Rules

| Rule | Antecedents | Consequent | Notes |
|------|-------------|------------|-------|
| STOP | P is not FALSE; H ⊢ ¬P ⇒ FALSE | H ⊢ P | Proved; ¬¬-elimination |

| Rule | Antecedents | Consequent | Result | Notes |
|------|-------------|------------|--------|-------|
| STOP′ | | H ⊢ P | P | `stop_r` in Res.lp; `result stop_r ↪ P` (identity) |

### A.11 INS Rule

| Rule | Antecedents | Consequent | Notes |
|------|-------------|------------|-------|
| INS | Determination of instantiations Q₁, ..., Qₙ; H ⊢ Q₁ ⇒ (Q₂ ⇒ ... (Qₙ ⇒ FALSE) ...) | H ⊢ FALSE | Proved; LP: `π ⊥ → π P` (ex falso); instantiation search is a side condition handled by the emitter |

### A.12 Normalisation

| Rule | Antecedents | Consequent | Notes |
|------|-------------|------------|-------|
| NRM1 | x not free in P; H ⊢ P ⇒ S | H ⊢ (♢x · P) ⇒ S | Proved |
| NRM2 | x not free in P; H ⊢ (P ⇒ ♢x · Q) ⇒ S | H ⊢ ♢x · (P ⇒ Q) ⇒ S | Proved |
| NRM3 | x not free in Q; Q is not FALSE; H ⊢ (Q ⇒ S) ∧ ((∀x · ¬P) ⇒ S) | H ⊢ ♢x · (P ⇒ Q) ⇒ S | Proved |
| NRM4 | x not free in Q; H ⊢ (Q ⇒ ♢x · (P ⇒ R)) ⇒ S | H ⊢ ♢x · (P ⇒ (Q ⇒ R)) ⇒ S | Proved |
| NRM5 | H ⊢ ♢x · (P ∧ Q ⇒ R) ⇒ S | H ⊢ ♢x · (P ⇒ (Q ⇒ R)) ⇒ S | Proved; also NRM5_2 for 2 variables |
| NRM6 | H ⊢ ♢x · (R ⇒ P) ⇒ (♢x · (R ⇒ Q) ⇒ S) | H ⊢ ♢x · (R ⇒ P ∧ Q) ⇒ S | Proved |
| NRM7 | H ⊢ (♢x · P) ⇒ ((♢x · Q) ⇒ S) | H ⊢ ♢x · (P ∧ Q) ⇒ S | Proved; also NRM7_2 for 2 variables |
| NRM8 | x and y are distinct; H ⊢ (♢(x, y) · Q) ⇒ S | H ⊢ (♢x · ∀y · Q) ⇒ S | Proved; **identity in HOAS** (♢ ≡ ∀ by rewrite rule) |
| NRM8 | x and y not distinct; z distinct from x and y; K = [y := z] Q; H ⊢ (♢(x, y) · K) ⇒ S | H ⊢ (♢x · ∀y · Q) ⇒ S | **HOAS**: α-equivalence — same LP rule handles both |
| NRM9 | x and y distinct; y not free in P; H ⊢ ♢(x, y) · (P ⇒ Q) ⇒ S | H ⊢ ♢x · (P ⇒ ∀y · Q) ⇒ S | Proved |
| NRM9 | x and y not distinct or y free in P; ... | H ⊢ ♢x · (P ⇒ ∀y · Q) ⇒ S | **HOAS**: α-equivalence — same LP rule handles both |
| NRM10 | H ⊢ ♡x · ¬(P ∧ Q) ⇒ R | H ⊢ ♢x · (P ∧ Q ⇒ FALSE) ⇒ R | **Admitted** |
| NRM11 | H ⊢ ♡x · ¬(TRUE ∧ P) ⇒ R | H ⊢ ♢x · (P ⇒ FALSE) ⇒ R | **Admitted** |
| NRM12 | H ⊢ ♡x · ¬(P ∧ Q) ⇒ R | H ⊢ ♢x · (P ⇒ ¬Q) ⇒ R | Proved |
| NRM13 | H ⊢ ♡x · ¬(P ∧ ¬Q) ⇒ R | H ⊢ ♢x · (P ⇒ Q) ⇒ R | Proved; also NRM13_2 for 2 variables |
| NRM14 | H ⊢ ♡x · ¬(TRUE ∧ P) ⇒ R | H ⊢ (♢x · ¬P) ⇒ R | Proved; also NRM14_2 for 2 variables |
| NRM15 | H ⊢ ♡x · ¬(TRUE ∧ ¬P) ⇒ R | H ⊢ (♢x · P) ⇒ R | Proved; also NRM15_2 for 2 variables |
| NRM16 | ∀x · P is in H | H ⊢ (♡x · P) ⇒ Q | Proved; LP takes `π (∀x, P x)` + `π Q` as explicit premises |
| NRM17 | ∀x · ¬(TRUE ∧ P) is in H; there exists E such that [x := E] P = R | H ⊢ ♡y · ¬(TRUE ∧ ¬R) ⇒ Q | LP type differs: `π (∀x, P x) → π Q → π ((♡x, P x) ⇒ Q)` — same implementation as NRM16 |
| NRM18 | ∀x · ¬(TRUE ∧ ¬P) is in H; there exists E such that [x := E] P = R | H ⊢ ♡y · ¬(TRUE ∧ R) ⇒ Q | **Admitted** |
| NRM19 | P is in H; there exists E such that [x := E] R = P | H ⊢ ♡x · ¬(TRUE ∧ R) ⇒ Q | Proved; LP: `π (R E) → π ((♡x, ¬(⊤ ∧ R x)) ⇒ Q)`; also NRM19_2 for 2 vars |
| NRM20 | x not free in E; H ⊢ ♡y · ¬[x := E]P ⇒ Q | H ⊢ ♡(x, y) · ¬(P ∧ x = E) ⇒ Q | Proved; HOAS handles substitution |
| NRM21 | x not free in E; H ⊢ ♡y · ¬[x := E]P ⇒ Q | H ⊢ ♡(x, y) · ¬(P ∧ E = x) ⇒ Q | Proved |
| NRM22 | x not free in E; H ⊢ ¬[x := E]P ⇒ Q | H ⊢ ♡x · ¬(P ∧ x = E) ⇒ Q | Proved |
| NRM23 | x not free in E; H ⊢ ¬[x := E]P ⇒ Q | H ⊢ ♡x · ¬(P ∧ E = x) ⇒ Q | Proved |
| NRM24 | P is not of the form A ∧ B; H ⊢ ♡x · ¬(TRUE ∧ P) ⇒ Q | H ⊢ ♡x · ¬P ⇒ Q | Proved |
| NRM25 | x not free in P; H ⊢ P | H ⊢ ♡(x) · P | Proved |
| NRM26 | y not free in P; H ⊢ ♡(x, ...) · P | H ⊢ ♡(x, y, ...) · P | Proved |
| NRM27 | (xᵢ ≤ 0) and (−xᵢ ≤ 0) in (P ∧...∧ Q); R = [xᵢ := 0](P ∧...∧ Q); H ⊢ ♢(x₁,...,xᵢ₋₁,xᵢ₊₁,...,xₙ) · ¬R | H ⊢ ♡(x₁,...,xₙ) · ¬(P ∧...∧ Q) | **Not encoded** — arithmetic normalisation |
| NRM28 | (x ≤ 0) and (−x ≤ 0) in (P ∧...∧ Q); S = [x := 0](P ∧...∧ Q); H ⊢ ¬(S) ⇒ R | H ⊢ (♡(x) · ¬(P ∧...∧ Q)) ⇒ R | **Not encoded** — arithmetic normalisation |
| NRM29 | (a + xᵢ ≤ 0) and (b − xᵢ ≤ 0) in (P ∧...∧ Q); solver(a+b) = 0; S = [xᵢ := b](P ∧...∧ Q); H ⊢ ♢(...) · ¬S ⇒ R | H ⊢ (♡(x₁,...,xₙ) · ¬(P ∧...∧ Q)) ⇒ R | **Not encoded** — arithmetic normalisation |
| NRM29_1 | (xᵢ + a ≤ 0) and (−xᵢ + b ≤ 0) in (P ∧...∧ Q); solver(a+b) = 0; S = [xᵢ := b](P ∧...∧ Q); H ⊢ ♢(...) · ¬S ⇒ R | H ⊢ (♡(x₁,...,xₙ) · ¬(P ∧...∧ Q)) ⇒ R | **Not encoded** — arithmetic normalisation |
| NRM30 | (a + x ≤ 0) and (b − x ≤ 0) in (P ∧...∧ Q); solver(a+b) = 0; S = [x := b](P ∧...∧ Q); H ⊢ ¬S ⇒ R | H ⊢ (♡x · ¬(P ∧...∧ Q)) ⇒ R | **Not encoded** — arithmetic normalisation |
| NRM30_1 | (x + a ≤ 0) and (−x + b ≤ 0) in (P ∧...∧ Q); solver(a+b) = 0; S = [x := b](P ∧...∧ Q); H ⊢ ¬S ⇒ R | H ⊢ (♡x · ¬(P ∧...∧ Q)) ⇒ R | **Not encoded** — arithmetic normalisation |

### A.13 Rules on Equalities

| Rule | Antecedents | Consequent | Notes |
|------|-------------|------------|-------|
| EVR1 | | H ⊢ ¬(E = E) ⇒ P | Proved |
| EVR2 | H ⊢ FALSE | H ⊢ ¬(E = E) | Proved |
| EVR3 | H ⊢ P | H ⊢ (E = E) ⇒ P | Proved |
| EVR4 | | H ⊢ (E = E) | Proved |
| EVR11 | n ∈ ℕ; m ∈ ℕ; n ≠ m | H ⊢ (n = m) ⇒ P | Proved; LP takes `π (n ϵ NAT)`, `π (m ϵ NAT)`, `π (n ≠ m)` |
| EAXM1 | ¬(F = E) is in H | H ⊢ (E = F) ⇒ P | Proved; LP takes `π (¬(F = E))` — equality symmetry |
| EAXM2 | (F = E) is in H | H ⊢ ¬(E = F) ⇒ P | Proved |
| EAXM31 | (F = E) is in H | H ⊢ (E = F) | Proved; equality symmetry |
| EAXM32 | ¬(F = E) is in H | H ⊢ ¬(E = F) | Proved |
| EIMP51 | ¬(F = E) is in H; H ⊢ P | H ⊢ ¬(E = F) ⇒ P | Proved |
| EIMP52 | (F = E) is in H; H ⊢ P | H ⊢ (E = F) ⇒ P | Proved |
| EQC1 | H ⊢ ¬(a = c) ∨ ¬(b = d) ⇒ P | H ⊢ ¬((a, b) = (c, d)) ⇒ P | Proved; uses pair injectivity axiom from B.lp |
| EQC2 | H ⊢ (a = c) ∧ (b = d) ⇒ P | H ⊢ ((a, b) = (c, d)) ⇒ P | Proved; uses pair injectivity axiom from B.lp |
| EQS1 | H ⊢ E = F ⇒ R | H ⊢ eql_set(E, F) ⇒ R | Proved; eql_set defined as `∀a, (a ϵ E) ⇔ (a ϵ F)` — uses set extensionality axiom |
| EQS2 | H ⊢ FALSE ⇒ R | H ⊢ ¬eql_set(E, F) ⇒ R | Proved |
| EAXM91 | ∀x · ¬(TRUE ∧ p = q) is in H; there exists E such that [x := E](q = p) reduces to (a = b) | H ⊢ (a = b) ⇒ Q | Proved; LP swaps equality order via symmetry |
| EAXM92 | ∀x · ¬(TRUE ∧ ¬(p = q)) is in H; there exists E such that [x := E](q = p) reduces to (a = b) | H ⊢ ¬(a = b) ⇒ Q | Proved |
| OPR1 | x is a variable; x not free in H; x not free in E; Q = [x := E] P; H ⊢ Q | H ⊢ (x = E) ⇒ P | Proved; HOAS: `π (P E) → π ((x = E) ⇒ P x)` — substitution via rewrite |
| OPR2 | x is a variable; x not free in H; x not free in E; Q = [x := E] P; H ⊢ Q | H ⊢ (E = x) ⇒ P | Proved |
| ECTR1 | ¬Q is in H; replacing E by F in Q gives R; R is in H | H ⊢ (E = F) ⇒ P | Proved; LP: `π (¬(Q E)) → π (Q F) → π ((E = F) ⇒ P)` |
| ECTR2 | ¬Q is in H; replacing E by F in Q gives R; R is in H | H ⊢ (F = E) ⇒ P | Proved |
| ECTR3 | E = F is in H; replacing E by F in P gives R; R is in H | H ⊢ ¬P ⇒ Q | Proved |
| ECTR4 | F = E is in H; replacing E by F in P gives R; R is in H | H ⊢ ¬P ⇒ Q | Proved |
| ECTR5 | E = F is in H; replacing E by F in P gives R; ¬R is in H | H ⊢ P ⇒ Q | Proved |
| ECTR6 | F = E is in H; replacing E by F in P gives R; ¬R is in H | H ⊢ P ⇒ Q | Proved |

### A.14 Rules on Arithmetic

| Rule | Antecedents | Consequent | Notes |
|------|-------------|------------|-------|
| AR1 | H ⊢ R | H ⊢ E ≤ E ⇒ R | Proved |
| AR2 | a is numeric; b is numeric; a > b | H ⊢ a ≤ b ⇒ R | **Admitted**; side condition is numeric check |
| AR3 | H ⊢ 1 − a ≤ 0 ⇒ R | H ⊢ ¬(a ≤ 0) ⇒ R | **Admitted**; side condition encoded as `π ⊤` |
| AR4 | F ≤ 0 is in H; E + F > 0 | H ⊢ E ≤ 0 ⇒ R | **Admitted**; side condition encoded as `π ⊤` |
| AR5 | a ≪ 0 is in H; H ⊢ a = 0 ⇒ (−a ≤ 0 ⇒ R) | H ⊢ −a ≤ 0 ⇒ R | **Admitted**; child type uses ≪ but proof needs ≤ — structural gap |
| AR6 | −a ≪ 0 is in H; H ⊢ a = 0 ⇒ (a ≤ 0 ⇒ R) | H ⊢ a ≤ 0 ⇒ R | **Admitted**; same structural gap as AR5 |
| AR7 | c + b ≪ 0 is in H; a + c = 0; H ⊢ a = b ⇒ (a − b ≪ 0 ⇒ R) | H ⊢ a − b ≤ 0 ⇒ R | **Admitted** |
| AR8 | a − b ≪ 0 is in H; a + c = 0; H ⊢ a = b ⇒ (c + b ≪ 0 ⇒ R) | H ⊢ c + b ≤ 0 ⇒ R | **Admitted** |
| AR9 | solver(E) = F; H ⊢ F ≤ 0 ⇒ R | H ⊢ E ≤ 0 ⇒ R | Proved; LP: `π (E = F) → π ((F ≤ 0) ⇒ R) → π ((E ≤ 0) ⇒ R)` — solver equality is explicit premise |
| AR10 | solver(P) = Q; H ⊢ Q ⇒ R | H ⊢ P ⇒ R | Proved; LP: `π (P = Q) → π (Q ⇒ R) → π (P ⇒ R)` |
| AR11 | | H ⊢ not(x ≤ x) ⇒ P | Proved |
| AR12 | H, (a ≤ b) ⊢ P | H ⊢ (a ≪ b) ⇒ P | Proved; HOAS: `(π (a ≤ b) → π P) → π ((a ≪ b) ⇒ P)` |
| AR13 | *(not in spec)* | | **Admitted**; `π ((1 - a) = b) → π (b ≤ 0) → π (¬(a ≪ 0))` — solver-derived bound |

### A.15 Rules on Booleans

| Rule | Antecedents | Consequent | Notes |
|------|-------------|------------|-------|
| BOOL11 | H, (v = TRUE), ¬(v = FALSE) ⊢ P | H ⊢ (v = TRUE) ⇒ P | Proved; HOAS: context extension via `bool_cases` |
| BOOL12 | H, (v = FALSE), ¬(v = TRUE) ⊢ P | H ⊢ (v = FALSE) ⇒ P | Proved |
| BOOL21 | H ⊢ (v = TRUE) ⇒ P | H ⊢ (TRUE = v) ⇒ P | Proved; equality symmetry |
| BOOL22 | H ⊢ (v = FALSE) ⇒ P | H ⊢ (FALSE = v) ⇒ P | Proved |
| BOOL31 | H ⊢ (v = FALSE) ⇒ P | H ⊢ ¬(v = TRUE) ⇒ P | Proved; **LP requires extra `v ∈ BOOL` premise** not in spec — emitter must find it in context |
| BOOL32 | H ⊢ (v = TRUE) ⇒ P | H ⊢ ¬(v = FALSE) ⇒ P | Proved; **LP requires extra `v ∈ BOOL` premise** |
| BOOL41 | H ⊢ (v = FALSE) ⇒ P | H ⊢ ¬(TRUE = v) ⇒ P | Proved; **LP requires extra `v ∈ BOOL` premise** |
| BOOL42 | H ⊢ (v = TRUE) ⇒ P | H ⊢ ¬(FALSE = v) ⇒ P | Proved; **LP requires extra `v ∈ BOOL` premise** |
| BOOL51 | | H ⊢ (TRUE = FALSE) ⇒ P | Proved; uses `bool_distinct` |
| BOOL52 | | H ⊢ ¬(FALSE = TRUE) ⇒ P | Proved; uses `bool_distinct` |
