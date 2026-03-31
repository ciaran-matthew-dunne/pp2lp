# B-Book Reference: Part I -- Mathematics

Reference for Jean-Raymond Abrial's *The B-Book*, Part I (Chapters 1--3).
Covers mathematical reasoning, set notation, and mathematical objects.

---

## 1. Mathematical Reasoning

### 1.1 Sequents and Inference

**Sequent**: `HYP |- P` -- hypotheses HYP entail conclusion P.

**Rule of inference**: antecedent sequents above the line, consequent below. Used forward (derivation) or backward (reduction). An **axiom** has no antecedents.

**Proof**: repeatedly apply rules backward until all leaves are axioms. A proved sequent is a **theorem** and can be reused as a rule. A **derived rule** is a proved rule of inference.

**Contradictory hypotheses**: HYP is contradictory if it proves both P and ¬P for some P; then any Q is provable.

#### Basic Rules

| Rule | Statement |
|------|-----------|
| BR 1 (axiom) | `P \|- P` |
| BR 2 | HYP ⊆ HYP' and `HYP \|- P` ⟹ `HYP' \|- P` (monotonicity) |
| BR 3 | P ∈ HYP ⟹ `HYP \|- P` (hypothesis rule, from BR1+BR2) |
| BR 4 | `HYP \|- P` and `HYP, P \|- Q` ⟹ `HYP \|- Q` (cut) |

### 1.2 Propositional Calculus

#### Syntax

Primary connectives: `¬` (negation, unary), `∧` (conjunction), `⇒` (implication).

Derived connectives:
- `P ∨ Q` ≝ `¬P ⇒ Q`
- `P ⇔ Q` ≝ `(P ⇒ Q) ∧ (Q ⇒ P)`

**Operator priority** (decreasing): `.` `[x:=E]` `¬` `∧` `∨` `⇒` `⇔`

#### Inference Rules

| Rule | Name | Statement |
|------|------|-----------|
| 1 (CNJ) | ∧-intro | `HYP \|- P` and `HYP \|- Q` ⟹ `HYP \|- P ∧ Q` |
| 2 / 2' | ∧-elim | `HYP \|- P ∧ Q` ⟹ `HYP \|- P` (resp. Q) |
| 3 (DED) | deduction | `HYP, P \|- Q` ⟹ `HYP \|- P ⇒ Q` |
| 4 | ⇒-elim | `HYP \|- P ⇒ Q` ⟹ `HYP, P \|- Q` |
| 5 | contradiction | `HYP, ¬Q \|- P` and `HYP, ¬Q \|- ¬P` ⟹ `HYP \|- Q` |
| 6 | contradiction | `HYP, Q \|- P` and `HYP, Q \|- ¬P` ⟹ `HYP \|- ¬Q` |

**Modus Ponens** (MP, derived): `HYP \|- P` and `HYP \|- P ⇒ Q` ⟹ `HYP \|- Q`

#### Derived Rules DR 1--8

| DR | From theorem | Effect |
|----|-------------|--------|
| 1 | `P ⇒ ¬¬P` | double negation intro |
| 2 | `P ∧ ¬Q ⇒ ¬(P ⇒ Q)` | negated implication |
| 3 | `(P ⇒ ¬Q) ⇒ ¬(P ∧ Q)` | negated conjunction |
| 4 | `(P ⇒ R) ⇒ (¬¬P ⇒ R)` | double negation elim in antecedent |
| 5 | `(P ⇒ (¬Q ⇒ R)) ⇒ (¬(P ⇒ Q) ⇒ R)` | |
| 6 | `(¬P ⇒ R) ∧ (¬Q ⇒ R) ⇒ (¬(P ∧ Q) ⇒ R)` | |
| 7 | `(¬P ⇒ R) ∧ (Q ⇒ R) ⇒ ((P ⇒ Q) ⇒ R)` | |
| 8 | `(P ⇒ (Q ⇒ R)) ⇒ (P ∧ Q ⇒ R)` | uncurry |

#### Proof Procedure

Apply rules backward in order: BS1, BS2, DB1, DB2, DR1..DR8, CNJ, DED. DED only when nothing else applies. Proof by cases (CASE): from `P ∨ Q`, prove R assuming P and R assuming Q.

#### Classical Laws

- **Commutativity**: `∧`, `∨`, `⇔`
- **Associativity**: `∧`, `∨`
- **Distributivity**: `R ∧ (P ∨ Q) ⇔ (R ∧ P) ∨ (R ∧ Q)`, etc.
- **De Morgan**: `¬(P ∨ Q) ⇔ ¬P ∧ ¬Q`; `¬(P ∧ Q) ⇔ ¬P ∨ ¬Q`
- **Contraposition**: `(P ⇒ Q) ⇔ (¬Q ⇒ ¬P)`
- **Double negation**: `P ⇔ ¬¬P`
- **Excluded middle**: `P ∨ ¬P`
- **Equivalence substitution**: `(P ⇔ Q) ⇒ (P ∧ R ⇔ Q ∧ R)`, etc.

### 1.3 Predicate Calculus

#### Syntax Extensions

- `∀x · P` -- universal quantification (x bound in P)
- `[x := E] F` -- substitution of E for free x in F
- `∃x · P` ≝ `¬∀x · ¬P`

#### Non-freeness

`x \\ F` means x has no free occurrences in F (either absent or only under quantifiers binding x).

| Rule | Statement | Condition |
|------|-----------|-----------|
| NF 1 | `x \\ y` | x ≠ y |
| NF 2 | `x \\ (P ∧ Q)` | `x \\ P` and `x \\ Q` |
| NF 3 | `x \\ (P ⇒ Q)` | `x \\ P` and `x \\ Q` |
| NF 4 | `x \\ (¬P)` | `x \\ P` |
| NF 5 | `x \\ ∀x · P` | always |
| NF 6 | `x \\ ∀y · P` | `x \\ y` and `x \\ P` |
| NF 7 | `x \\ [x := E] F` | `x \\ E` |
| NF 8 | `x \\ [y := E] F` | `x \\ y` and `x \\ E` and `x \\ F` |
| NF 9 | `x \\ (E = F)` | `x \\ E` and `x \\ F` |
| NF 10 | `(x,y) \\ E` | `x \\ E` and `y \\ E` |
| NF 11 | `x \\ (E, F)` | `x \\ E` and `x \\ F` |
| NF 12 | `x \\ ∀(y,z) · P` | `x \\ ∀y · ∀z · P` |

#### Substitution Rules

| Rule | LHS | RHS | Condition |
|------|-----|-----|-----------|
| SUB 1 | `[x := E] x` | `E` | |
| SUB 2 | `[x := E] y` | `y` | x ≠ y |
| SUB 3 | `[x := E] (P ∧ Q)` | `[x:=E]P ∧ [x:=E]Q` | |
| SUB 4 | `[x := E] (P ⇒ Q)` | `[x:=E]P ⇒ [x:=E]Q` | |
| SUB 5 | `[x := E] (¬P)` | `¬[x:=E]P` | |
| SUB 6 | `[x := E] ∀x · P` | `∀x · P` | |
| SUB 7 | `[x := E] ∀y · P` | `∀y · [x:=E]P` | y ≠ x and `y \\ E` |
| SUB 8 | `[x := x] F` | `F` | |
| SUB 9 | `[x := E] F` | `F` | `x \\ F` |
| SUB 10 | `[y := E] [x := y] F` | `[x := E] F` | `y \\ F` |
| SUB 11 | `[x := D] [y := E] F` | `[y := [x:=D]E] [x:=D]F` | `y \\ D` |
| SUB 12 | `[x := C] (D = E)` | `[x:=C]D = [x:=C]E` | |
| SUB 13 | `[x,y := C,D] F` | `[z:=D][x:=C][y:=z]F` | x ≠ y, z fresh |

**Change of variable**: if SUB 7 side-condition fails (y free in E), rename y to fresh z first.

#### Predicate Calculus Rules

| Rule | Name | Statement |
|------|------|-----------|
| 7 (GEN) | ∀-intro | `x \\ H` for all H in HYP, `HYP \|- P` ⟹ `HYP \|- ∀x · P` |
| 8 (ELIM) | ∀-elim | `HYP \|- ∀x · P` ⟹ `HYP \|- [x := E] P` |

#### Derived Rules DR 9--16

| DR | Statement |
|----|-----------|
| 9 | `x \\ R`, `x \\ H` ∀H∈HYP, `HYP \|- ¬P ⇒ R` ⟹ `HYP \|- ¬∀x·P ⇒ R` |
| 10 | `HYP \|- [x:=E]¬P` ⟹ `HYP \|- ¬∀x·P` |
| 11 | `∀x·P` ∈ HYP, `HYP \|- [x:=E]P ⇒ R` ⟹ `HYP \|- R` |
| 12 | `x \\ R`, `x \\ H` ∀H∈HYP, `HYP \|- P ⇒ R` ⟹ `HYP \|- ∃x·P ⇒ R` |
| 13 | `HYP \|- [x:=E]P` ⟹ `HYP \|- ∃x·P` (existential witness) |
| 14 | `HYP \|- ∀x·¬P` ⟹ `HYP \|- ¬∃x·P` |
| 15 | `HYP \|- [x:=E]¬P` ⟹ `HYP \|- ¬∃x·P` |
| 16 | `HYP \|- ∃x·¬¬P` ⟹ `HYP \|- ¬∀x·P` |

#### Predicate Calculus Classical Laws

- `∀x·∀y·P ⇔ ∀y·∀x·P` (commute quantifiers)
- `∀x·(P ∧ Q) ⇔ ∀x·P ∧ ∀x·Q`
- `∃x·(P ∨ Q) ⇔ ∃x·P ∨ ∃x·Q`
- `¬∀x·P ⇔ ∃x·¬P` (De Morgan for quantifiers)
- `P ∨ ∀x·Q ⇔ ∀x·(P ∨ Q)` if `x \\ P`
- `∀x·(P ⇒ Q) ⇒ (∀x·P ⇒ ∀x·Q)` (monotonicity)

### 1.4 Equality

#### Rules

| Rule | Name | Statement |
|------|------|-----------|
| 9 | Leibnitz | `HYP \|- E = F` and `HYP \|- [x:=E]P` ⟹ `HYP \|- [x:=F]P` |
| 10 (EQL) | reflexivity (axiom) | `HYP \|- E = E` |

Derived: symmetry (`E = F ⇒ F = E`), transitivity (`E = F ∧ F = G ⇒ E = G`).

#### One-Point Rules

- `∀x·(x = E ⇒ P) ⇔ [x:=E]P` if `x \\ E` (Thm 1.4.6)
- `∃x·(x = E ∧ P) ⇔ [x:=E]P` if `x \\ E` (Thm 1.4.7)

### 1.5 Ordered Pairs

- `E, F` or `E ↦ F` -- ordered pair (maplet syntax is sugar for comma)
- Multiple variables: `(x,y)`, multiple quantification: `∀(x,y) · P ⇔ ∀x · ∀y · P` (x ≠ y)
- Multiple substitution: `[x,y := C,D] F`
- `C,D = E,F ⇒ C = E ∧ D = F` (Thm 1.5.5)

---

## 2. Set Notation

### 2.1 Basic Set Constructs

#### Syntax

| Category | Constructs |
|----------|------------|
| Predicate | ... ∣ `E ∈ s` |
| Expression | ... ∣ `choice(s)` ∣ `s` (a Set is an Expression) |
| Set | `s × t` ∣ `ℙ(s)` ∣ `{x \| x ∈ s ∧ P}` ∣ `BIG` |

Key design: ordered pairs are NOT sets (unlike ZF). Sets are a distinct syntactic category.

#### Axioms

| Axiom | Statement |
|-------|-----------|
| SET 1 | `(E,F) ∈ s × t ⇔ E ∈ s ∧ F ∈ t` |
| SET 2 | `s ∈ ℙ(t) ⇔ ∀x·(x ∈ s ⇒ x ∈ t)` |
| SET 3 | `E ∈ {x \| x ∈ s ∧ P} ⇔ E ∈ s ∧ [x:=E]P` |
| SET 4 | `∀x·(x ∈ s ⇔ x ∈ t) ⇒ s = t` (extensionality) |
| SET 5 | `∃x·(x ∈ s) ⇒ choice(s) ∈ s` |
| SET 6 | `infinite(BIG)` |

**Set inclusion**: `s ⊆ t` ≝ `s ∈ ℙ(t)`; `s ⊂ t` ≝ `s ⊆ t ∧ s ≠ t`.

Properties: reflexivity, transitivity, anti-symmetry of ⊆; monotonicity of ℙ, ×.

#### Additional NF and SUB rules for sets

NF 13--18 extend non-freeness to `∈`, `choice`, `×`, `ℙ`, comprehension, `BIG`.
SUB 14--20 extend substitution similarly.

### 2.2 Type-Checking

Every predicate with set constructs must be type-checked before proving. This prevents ill-formed statements like `∃x·(x ∈ x)`. Type-checking is a decidable procedure using rules T1--T21 (and extensions).

Key concepts:
- **type(E)**: the type of an expression
- **super(s)**: the super-set of a set
- **given(I)**: a given set with `super(I) = I`

Quantified predicates must have the form `∀x·(x ∈ s ∧ ... ⇒ P)`. Comprehension sets must have the form `{x | x ∈ s ∧ ... ∧ P}`.

Core typing rules: T7 (`E = F` requires `type(E) = type(F)`), T8 (`E ∈ s` requires `type(E) = super(s)`), T9 (variable type from environment), T10 (`type(E ↦ F) = type(E) × type(F)`), T12 (`type(s) = ℙ(super(s))`), T14 (`super(s × t) = super(s) × super(t)`), T15 (`super(ℙ(s)) = ℙ(super(s))`).

### 2.3 Derived Constructs

Given `s, t ⊆ u`, `E ∈ u`:

| Syntax | Definition |
|--------|-----------|
| `s ∪ t` | `{a \| a ∈ u ∧ (a ∈ s ∨ a ∈ t)}` |
| `s ∩ t` | `{a \| a ∈ u ∧ a ∈ s ∧ a ∈ t}` |
| `s − t` | `{a \| a ∈ u ∧ a ∈ s ∧ a ∉ t}` |
| `{E}` | `{a \| a ∈ u ∧ a = E}` |
| `{L, E}` | `{L} ∪ {E}` |
| `∅` | `ℙ₁(BIG) − ℙ₁(BIG)` |
| `ℙ₁(s)` | `ℙ(s) − {∅}` |

Standard algebraic laws hold: commutativity, associativity, distributivity, De Morgan, idempotence, absorption, monotonicity of ∪, ∩, −, ×.

### 2.4 Binary Relations

Given `p ∈ u ↔ v`, `q ∈ v ↔ w`, `s ⊆ u`, `t ⊆ v`:

| Syntax | Definition | Description |
|--------|-----------|-------------|
| `u ↔ v` | `ℙ(u × v)` | relations from u to v |
| `p⁻¹` | `{b,a \| (a,b) ∈ p}` | inverse |
| `dom(p)` | `{a \| a ∈ u ∧ ∃b·(b ∈ v ∧ (a,b) ∈ p)}` | domain |
| `ran(p)` | `dom(p⁻¹)` | range |
| `p ; q` | forward composition | `{a,c \| ∃b·((a,b) ∈ p ∧ (b,c) ∈ q)}` |
| `id(u)` | `{a,b \| a ∈ u ∧ a = b}` | identity |
| `s ◁ p` | `id(s) ; p` | domain restriction |
| `p ▷ t` | `p ; id(t)` | range restriction |
| `s ⩤ p` | `(dom(p) − s) ◁ p` | domain subtraction |
| `p ⩥ t` | `p ▷ (ran(p) − t)` | range subtraction |

Second series:

| Syntax | Definition | Description |
|--------|-----------|-------------|
| `p[w]` | `ran(w ◁ p)` | image of set w under p |
| `q <+ p` | `(dom(p) ⩤ q) ∪ p` | override of q by p |
| `f ⊗ g` | `{a,(b,c) \| (a,b) ∈ f ∧ (a,c) ∈ g}` | direct product |
| `prj₁(s,t)` | `(id(s) ⊗ (s × t))⁻¹` | first projection |
| `prj₂(s,t)` | `((t × s) ⊗ id(t))⁻¹` | second projection |
| `h ∥ k` | `{(a,b),(c,d) \| (a,c) ∈ h ∧ (b,d) ∈ k}` | parallel product |

Type-checking rules T29--T43 cover all relation constructs.

### 2.5 Functions

| Syntax | Definition |
|--------|-----------|
| `s ⇸ t` | `{r \| r ∈ s ↔ t ∧ r⁻¹;r ⊆ id(t)}` -- partial functions |
| `s → t` | `{f \| f ∈ s ⇸ t ∧ dom(f) = s}` -- total functions |
| `s ⤔ t` | `{f \| f ∈ s ⇸ t ∧ f⁻¹ ∈ t ⇸ s}` -- partial injections |
| `s ↣ t` | `s → t ∩ s ⤔ t` -- total injections |
| `s ⇸ t` | partial surjections (`ran(f) = t`) |
| `s ↠ t` | total surjections |
| `s ⤀ t` | partial bijections (injection + surjection) |
| `s ⤖ t` | total bijections |

**Function application**: `f(E)` ≝ `choice(f[{E}])`, requires `f ∈ s ⇸ t` and `E ∈ dom(f)`.

**Lambda abstraction**:
- `λx·(x ∈ s | E)` ≝ `{x,y | (x,y) ∈ s × t ∧ y = E}`, requires `∀x·(x ∈ s ⇒ E ∈ t)`
- `λx·(x ∈ s ∧ P | E)` -- with guard predicate

**Key properties**:
- `f ∈ s ⇸ t ∧ x ∈ dom(f) ⇒ (x, f(x)) ∈ f` (Property 2.5.2)
- `λx·(x ∈ s | E) ∈ s → t` when `∀x·(x ∈ s ⇒ E ∈ t)` (Property 2.5.3)
- `λx·(x ∈ s | E)(V) = [x := V]E` when `V ∈ s` (Theorem 2.5.1)
- `f ∈ s → t ⇔ ∀x·(x ∈ s ⇒ {x} ◁ f ∈ {x} → t)` (Property 2.5.1)
- `(x,y) ∈ f ⇔ x ∈ dom(f) ∧ y = f(x)` (Property 2.5.4)

### 2.6 Catalogue of Properties

Extensive catalogue of laws organized by operator. Key categories:

**Membership laws**: typing of `r⁻¹`, `dom`, `ran`, `p;q`, `id`, restrictions, image, override, `⊗`, `∥` under various function/relation spaces.

**Domain/range laws**: `dom(f) = s` for `f ∈ s → t`; `dom(p;q) = p⁻¹[dom(q)]`; `dom(s ◁ r) = s ∩ dom(r)`; distributivity over ∪, ∩, −, `<+`, `⊗`, `∥`.

**Composition laws**: `r ; id(t) = r`; `f ; (p <+ q) = (f;p) <+ (f;q)` for functional f; `(p ∪ q) ; r = (p;r) ∪ (q;r)`; `f⁻¹;f = id(ran(f))` for functional f.

**Restriction laws**: `u ◁ (r;p) = (u ◁ r);p`; `dom(r) ◁ r = r`; `f⁻¹[v] ◁ f = f ▷ v`.

**Identity laws**: `id(u ∪ v) = id(u) ∪ id(v)`; `id(u) ; id(v) = id(u ∩ v)`.

---

## 3. Mathematical Objects

### 3.1 Generalized Intersection and Union

Given `u ∈ ℙ₁(ℙ(s))` (resp. `u ∈ ℙ(ℙ(s))`):

| Syntax | Definition |
|--------|-----------|
| `inter(u)` | `{x \| x ∈ s ∧ ∀y·(y ∈ u ⇒ x ∈ y)}` (u must be non-empty) |
| `union(u)` | `{x \| x ∈ s ∧ ∃y·(y ∈ u ∧ x ∈ y)}` |

Quantified forms (x ∈ s, E a set expression depending on x):
- `⋂x·(x ∈ s | E)` = `{y | y ∈ t ∧ ∀x·(x ∈ s ⇒ y ∈ E)}`
- `⋃x·(x ∈ s | E)` = `{y | y ∈ t ∧ ∃x·(x ∈ s ∧ y ∈ E)}`

**Properties**:
- `inter(u)` is the greatest lower bound (glb) of members of u (Thms 3.1.1, 3.1.2)
- `union(u)` is the least upper bound (lub) of members of u (Thms 3.1.3, 3.1.4)
- `inter({a,b}) = a ∩ b`; `union({a,b}) = a ∪ b`
- `inter(a ∪ b) = inter(a) ∩ inter(b)` (a,b non-empty)
- Associativity and distributivity with nested quantifiers

### 3.2 Fixpoints and Induction

#### Fixpoint Operators

Given `f ∈ ℙ(s) → ℙ(s)`:

| Syntax | Definition |
|--------|-----------|
| `fix(f)` | `inter({x \| x ∈ ℙ(s) ∧ f(x) ⊆ x})` -- least fixpoint |
| `FIX(f)` | `union({x \| x ∈ ℙ(s) ∧ x ⊆ f(x)})` -- greatest fixpoint |

**Knaster-Tarski Theorem** (Thm 3.2.5/3.2.6): If f is monotone (`a ⊆ b ⇒ f(a) ⊆ f(b)`), then `f(fix(f)) = fix(f)` and `f(FIX(f)) = FIX(f)`. Moreover, `fix(f)` is the least fixpoint and `FIX(f)` is the greatest.

Key inclusion principles:
- `f(t) ⊆ t ⇒ fix(f) ⊆ t` (Thm 3.2.1)
- `t ⊆ f(t) ⇒ t ⊆ FIX(f)` (Thm 3.2.3)

#### General Induction Principle

To prove `∀x·(x ∈ fix(f) ⇒ P)`, it suffices to prove `f({x | x ∈ fix(f) ∧ P}) ⊆ {x | x ∈ fix(f) ∧ P}` (Thm 3.2.7).

**First special case** (f(z) = {a} ∪ g[z], a ∈ s, g ∈ s → s):
- `fix(f) = {a} ∪ g[fix(f)]`
- Induction (Thm 3.2.8): prove `[x:=a]P` (base) and `∀x·(x ∈ fix(f) ∧ P ⇒ [x:=g(x)]P)` (step)

**Second special case** (f(z) = {a} ∪ g[t × z], a ∈ s, g ∈ t × s → s):
- Induction (Thm 3.2.9): prove `[x:=a]P` (base) and `∀x·(x ∈ fix(f) ∧ P ⇒ ∀u·(u ∈ t ⇒ [x:=g(u,x)]P))` (step)

### 3.3 Finite Subsets

| Syntax | Definition |
|--------|-----------|
| `add(s)` | `λ(u,x)·((u,x) ∈ s × ℙ(s) \| {u} ∪ x)` |
| `genfin(s)` | `λz·(z ∈ ℙ(ℙ(s)) \| {∅} ∪ add(s)[s × z])` |
| `𝔽(s)` | `fix(genfin(s))` |
| `𝔽₁(s)` | `𝔽(s) − {∅}` |

Properties: `∅ ∈ 𝔽(s)`, `(u,x) ∈ s × 𝔽(s) ⇒ {u} ∪ x ∈ 𝔽(s)`.

**Finite set induction** (Thm 3.3.1): prove `[x:=∅]P` and `∀x·(x ∈ 𝔽(s) ∧ P ⇒ ∀u·(u ∈ s ⇒ [x:={u} ∪ x]P))`.

Key results: union of two finite sets is finite; intersection of two finite sets is finite; image of finite set under partial function is finite.

### 3.4 Finite and Infinite Sets

- `finite(s)` ≝ `s ∈ 𝔽(s)`
- `infinite(s)` ≝ `¬finite(s)`
- `BIG` is infinite (axiom SET 6)
- `infinite(s) ∧ t ∈ 𝔽(s) ⇒ s − t ≠ ∅` (cannot exhaust infinite set by finite means)
- Dedekind infinite ⇒ infinite (Thm 3.4.1): `∃f·(f ∈ s ↣ s ∧ ran(f) ⊂ s) ⇒ infinite(s)`

### 3.5 Natural Numbers

#### Definition

| Syntax | Definition |
|--------|-----------|
| `0` | `BIG − BIG` |
| `succ` | `λn·(n ∈ 𝔽(BIG) \| {choice(n̄)} ∪ n)` where `n̄ = BIG − n` |
| `genat` | `λs·(s ∈ ℙ(𝔽(BIG)) \| {0} ∪ succ[s])` |
| `ℕ` | `fix(genat)` |
| `1` | `succ(0)` |
| `ℕ₁` | `ℕ − {0}` |
| `pred` | `succ⁻¹ ▷ ℕ` |

Order: `n ≤ m` ≝ `n ⊆ m`; `n < m` ≝ `n ≠ m ∧ n ≤ m`.

Relations: `gtr`, `geq`, `lss`, `leq` defined as expected.

#### Peano's Axioms (proved as theorems)

1. `0 ∈ ℕ`
2. `∀n·(n ∈ ℕ ⇒ succ(n) ∈ ℕ)`
3. `∀n·(n ∈ ℕ ⇒ succ(n) ≠ 0)`
4. `pred ∈ ℕ ⤖ ℕ₁` (succ is injective on ℕ)
5. Mathematical induction (Thm 3.5.1)

**Mathematical induction**: `[n:=0]P ∧ ∀n·(n ∈ ℕ ∧ P ⇒ [n:=succ(n)]P) ⇒ ∀n·(n ∈ ℕ ⇒ P)`

**Strong induction** (Thm 3.5.2): `∀n·(n ∈ ℕ ∧ ∀m·(m ∈ ℕ ∧ m < n ⇒ [n:=m]P) ⇒ P) ⇒ ∀n·(n ∈ ℕ ⇒ P)`

#### Min, Max

- `min(s)` ≝ `inter(s)` for `s ∈ 𝔽₁(ℕ)`. Is glb AND member of s (Property 3.5.9).
- `max(s)` ≝ `union(s)` for `s ∈ 𝔽₁(ℕ)`. Is lub AND member of s (Property 3.5.11).
- ≤ on ℕ is a well-ordering (every non-empty subset has a least member).

#### Recursion on ℕ

Given `a ∈ s`, `g ∈ s → s`, there exists a unique `f ∈ ℕ → s` with `f(0) = a` and `f(succ(n)) = g(f(n))` (Thm 3.5.3).

#### Arithmetic

Recursive definitions:

| Op | Base | Step |
|----|------|------|
| `m + n` | `plus(m)(0) = m` | `plus(m)(succ(n)) = succ(plus(m)(n))` |
| `m × n` | `mult(m)(0) = 0` | `mult(m)(succ(n)) = m + (m × n)` |
| `mⁿ` | `exp(m)(0) = 1` | `exp(m)(succ(n)) = m × mⁿ` |

Standard properties: commutativity, associativity, distributivity of +, ×; `m + 0 = m`, `m × 1 = m`, etc.

Subtraction: `n − m` ≝ `plus(m)⁻¹(n)` for `m ≤ n`.

Division: `n / m` ≝ `min({x | x ∈ ℕ ∧ n < m × succ(x)})` for m ≥ 1. Satisfies `m × q ≤ n < m × succ(q)` where `q = n / m`. Remainder: `n mod m` ≝ `n − m × (n / m)`.

Logarithm: `logₘ(n)` ≝ `min({x | x ∈ ℕ ∧ n < m^succ(x)})` for m > 1. Satisfies `mˡ ≤ n < m^succ(l)`.

#### Iterate of a Relation

`r⁰ = id(s)`, `r^succ(n) = r ; rⁿ`. Properties: `r¹ = r`, `p ⊆ q ⇒ pⁿ ⊆ qⁿ`, `r[a] ⊆ a ⇒ rⁿ[a] ⊆ a`.

#### Cardinal

`card(t)` ≝ `min({n | n ∈ ℕ ∧ t ∈ genfin(s)ⁿ({∅})})` for `t ∈ 𝔽(s)`.

#### Transitive Closures

| Syntax | Definition |
|--------|-----------|
| `r*` | `fix(λh·(h ∈ ℙ(s×s) \| id(s) ∪ (r;h)))` -- reflexive transitive closure |
| `r⁺` | `fix(λh·(h ∈ ℙ(s×s) \| r ∪ (r;h)))` -- transitive closure |

Properties: `r* = ⋃n·(n ∈ ℕ | rⁿ)`; `r⁺ = ⋃n·(n ∈ ℕ₁ | rⁿ)`; `r* = id(s) ∪ r⁺`; `r*[a] = a ∪ r⁺[a]`.

Relational operators on ℕ: `gtr = succ⁺`, `geq = succ*`, `lss = pred⁺`, `leq = pred*`.

### 3.6 Integers

`ℤ` with `ℕ ⊆ ℤ`. Negative integers: `ℤ₁ = ℤ − ℕ`. Unary minus: `uminus ∈ ℤ ⤖ ℤ`, `−n = uminus(n)`. All arithmetic operators extended to ℤ with standard sign rules. `min` and `max` extended to finite subsets of ℤ.

### 3.7 Finite Sequences

#### Inductive Construction

| Syntax | Definition |
|--------|-----------|
| `x → f` | `{1 ↦ x} ∪ (pred ; f)` (insert x at beginning) |
| `seq(s)` | `fix(λz·(z ∈ ℙ(ℕ₁ ⇸ s) \| {[]} ∪ insert(s)[s × z]))` |
| `seq₁(s)` | `seq(s) − {[]}` |
| `iseq(s)` | `seq(s) ∩ (ℕ₁ ⤔ s)` -- injective sequences |
| `perm(s)` | `iseq(s) ∩ (ℕ₁ ↠ s)` -- permutations |

Properties: `[] ∈ seq(s)`, `(x,t) ∈ s × seq(s) ⇒ x → t ∈ seq(s)`.

**Induction** (Thm 3.7.1): prove `[t:=[]]P` and `∀t·(t ∈ seq(s) ∧ P ⇒ ∀x·(x ∈ s ⇒ [t:=x→t]P))`.

#### Direct Construction

`m .. n` ≝ `{p | p ∈ ℤ ∧ m ≤ p ∧ p ≤ n}` (integer interval).

`seq(s) = ⋃n·(n ∈ ℕ | (1..n) → s)`.

#### Operations (Recursive)

| Syntax | Base | Step |
|--------|------|------|
| `size([])` | `0` | `size(x→t) = size(t) + 1` |
| `[] ^ u` | `u` | `(x→t) ^ u = x → (t ^ u)` |
| `t ← y` | `[y]` for `[]` | `(x→t) ← y = x → (t ← y)` |
| `rev([])` | `[]` | `rev(x→t) = rev(t) ← x` |
| `conc([])` | `[]` | `conc(x→t) = x ^ conc(t)` |

Properties: `size(t^u) = size(t) + size(u)`, `rev(rev(t)) = t`, `rev(t^u) = rev(u) ^ rev(t)`, `t ^ (u ^ v) = (t ^ u) ^ v`.

#### Operations (Direct)

| Syntax | Definition | Description |
|--------|-----------|-------------|
| `t ↑ n` | `(1..n) ◁ t` | first n elements |
| `t ↓ n` | `plus(n) ; ((1..n) ⩤ t)` | drop first n elements |
| `first(t)` | `t(1)` | |
| `last(t)` | `t(size(t))` | |
| `tail(t)` | `t ↓ 1` | |
| `front(t)` | `t ↑ (size(t)−1)` | |

**Extensive definition**: `[E]` ≝ `{1 ↦ E}`, `[L,E]` ≝ `[L] ← E`.

#### Sorting

`sort ∈ seq(ℤ) → seq(ℤ)` defined recursively using a partition function. `sort([]) = []`, `sort(x→u) = sort(a) ^ [x] ^ sort(b)` where `(a,b) = partition(x)(u)`. Satisfies `u prm sort(u) ∧ sorted(sort(u))`.

#### Sums and Products

`∑x·(x ∈ s | E)` and `∏x·(x ∈ s | E)` via `sumf` and `prodf` applied to lambda abstractions over finite domains.

### 3.8--3.10 Trees

#### Finite Trees (T)

A tree is a finite, prefix-closed set of sequences of positive natural numbers. Constructed via `cns : seq(T) ↣ T` where `cns(⟨t₁,...,tₙ⟩)` inserts rank indices at the front of each node sequence. `T = cns[seq(T)]`. The function `sns = cns⁻¹ ▷ seq(T)` extracts the son sequence.

**Induction** (Thm 3.8.1): `∀t·(t ∈ T ∧ sns(t) ∈ seq({t | t ∈ T ∧ P}) ⇒ P) ⇒ ∀t·(t ∈ T ⇒ P)` (prove P for t assuming P holds for all sons).

**Recursion**: given `g ∈ seq(u) → u`, construct `f ∈ T → u` with `f(t) = g(sns(t);f)`.

#### Labelled Trees (tree(s))

`tree(s)` ≝ labelled trees on set s, constructed via `cons : s × seq(tree(s)) ↣ tree(s)`.

- `top ∈ tree(s) → s` -- root label
- `sons ∈ tree(s) → seq(tree(s))` -- son sequence
- `top ⊗ sons = cons⁻¹`

**Induction** (Thm 3.9.1): prove P for t assuming P holds for all elements of `sons(t)`.

**Recursion**: given `g ∈ s × seq(u) → u`, construct `f ∈ tree(s) → u` with `f(t) = g(top(t), sons(t);f)`.

Operations: `pre` (preorder), `post` (postorder), `sizet`, `mirror`. Property: `mirror ; pre = post ; rev`.

Direct operations: `rank`, `father`, `son`, `subt` (subtree at node), `arity`.

#### Binary Trees (bin(s))

`bin(s) ⊆ tree(s)`, each node has arity 0 or 2.
- `(x)` = `cons(x, [])` -- leaf
- `(l, x, r)` = `cons(x, [l, r])` -- node
- `left(t)` = `first(sons(t))`, `right(t)` = `last(sons(t))`

**Induction** (Thm 3.10.1): prove P for `(x)` (base), and for `(l,x,r)` assuming P for l and r (step).

**Recursion**: given `h ∈ s → u`, `g ∈ u × s × u → u`, construct `f ∈ bin(s) → u` with `f((x)) = h(x)`, `f((l,x,r)) = g(f(l), x, f(r))`.

Operations: `infix`, `pre`, `post` traversals.

### 3.11 Well-founded Relations

#### Definition

Given `r ∈ s ↔ s`:

`wfd(r)` ≝ `∀p·(p ∈ ℙ(s) ∧ p ⊆ r⁻¹[p] ⇒ p = ∅)`

Equivalently: no infinite descending chains through r. Every non-empty subset has an r-minimal element.

#### Induction on Well-founded Sets

`∀x·(x ∈ s ∧ ∀y·(y ∈ r[{x}] ⇒ P(y)) ⇒ P(x)) ⇒ ∀x·(x ∈ s ⇒ P(x))`

To prove P for all x in s: assume P holds for all y with `(x,y) ∈ r`, prove P(x).

#### Recursion on Well-founded Sets

Given `g ∈ (s ⇸ t) → t`, construct `f ∈ s → t` with `f(x) = g(r[{x}] ◁ f)`. Uses the fixpoint equation `f = g ∘ res(f) ∘ image(r)` where `image(r)(x) = r[{x}]` and `res(f)` restricts f appropriately. Existence via Knaster-Tarski (Thm 3.2.5).

#### Proving Well-foundedness (Thm 3.11.1)

Given `wfd(r)` on s, and `v ∈ s' ↔ s` with `dom(v) = s'` and `v⁻¹;r' ⊆ r;v⁻¹`, then `wfd(r')` on s'.

#### Example

The lexicographic order on `ℕ × ℕ` defined by `(a,b) r (c,d) ⇔ a > c ∨ (a = c ∧ b > d)` is well-founded. The Ackermann function is defined by recursion on this relation.
