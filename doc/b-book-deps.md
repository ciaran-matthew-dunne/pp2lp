# B-Book Dependencies for pp2lp

This file records the specific parts of J-R Abrial's *The B-Book*
(Cambridge University Press, ISBN 0-521-49619-5) that are referenced
by the PP specification (`spec_pp.md`) or used in our Lambdapi
encoding.

The PP specification references the B-Book as "Doc[1]" in four
places:

1. Chapter 2 of Doc[1] defines the set-theoretic syntax that the
   Set Translator handles (spec_pp.md Section 3.1, 3.2.3).
2. Chapter 3 of Doc[1] covers trees, which are NOT yet handled
   by the Set Translator.
3. Chapter 1 of Doc[1] is referenced for background on inference
   rules and proof procedures (spec_pp.md Section 6).

The remainder of this file records the specific rules and axioms
from the B-Book that are used in our Lambdapi code.

---

## Non-Freeness Rules (B-Book Section 1.3)

Used in `lp/NonFree.lp`. `x \\ F` means x has no free
occurrences in F.

| Rule | Statement | Condition |
|------|-----------|-----------|
| NF 1 | `x \\ y` | x != y |
| NF 2 | `x \\ (P & Q)` | `x \\ P` and `x \\ Q` |
| NF 3 | `x \\ (P => Q)` | `x \\ P` and `x \\ Q` |
| NF 4 | `x \\ (not P)` | `x \\ P` |
| NF 5 | `x \\ forall x . P` | always |
| NF 6 | `x \\ forall y . P` | `x \\ y` and `x \\ P` |
| NF 7 | `x \\ [x := E] F` | `x \\ E` |
| NF 8 | `x \\ [y := E] F` | `x \\ y`, `x \\ E`, `x \\ F` |
| NF 9 | `x \\ (E = F)` | `x \\ E` and `x \\ F` |
| NF 10 | `(x,y) \\ E` | `x \\ E` and `y \\ E` |
| NF 11 | `x \\ (E, F)` | `x \\ E` and `x \\ F` |
| NF 12 | `x \\ forall (y,z) . P` | `x \\ forall y . forall z . P` |
| NF 13-18 | extensions for set constructs | membership, choice, x, P, comprehension, BIG |

---

## Substitution Rules (B-Book Section 1.3)

Used in `lp/Subst.lp`.

| Rule | LHS | RHS | Condition |
|------|-----|-----|-----------|
| SUB 1 | `[x := E] x` | `E` | |
| SUB 2 | `[x := E] y` | `y` | x != y |
| SUB 3 | `[x := E] (P & Q)` | `[x:=E]P & [x:=E]Q` | |
| SUB 4 | `[x := E] (P => Q)` | `[x:=E]P => [x:=E]Q` | |
| SUB 5 | `[x := E] (not P)` | `not [x:=E]P` | |
| SUB 6 | `[x := E] forall x . P` | `forall x . P` | |
| SUB 7 | `[x := E] forall y . P` | `forall y . [x:=E]P` | y != x, `y \\ E` |
| SUB 8 | `[x := x] F` | `F` | |
| SUB 9 | `[x := E] F` | `F` | `x \\ F` |
| SUB 10 | `[y := E] [x := y] F` | `[x := E] F` | `y \\ F` |
| SUB 11 | `[x := D] [y := E] F` | `[y := [x:=D]E] [x:=D]F` | `y \\ D` |
| SUB 12 | `[x := C] (D = E)` | `[x:=C]D = [x:=C]E` | |
| SUB 14-20 | extensions for set constructs | membership, choice, x, P, comprehension |

---

## Set-Theoretic Axioms (B-Book Section 2.1)

Used in `lp/Ax.lp`.

| Axiom | Statement |
|-------|-----------|
| SET 1 | `(E,F) : s x t <=> E : s & F : t` |
| SET 2 | `s : P(t) <=> forall x . (x : s => x : t)` |
| SET 3 | `E : {x \| x : s & P} <=> E : s & [x:=E]P` |
| SET 4 | `forall x . (x : s <=> x : t) => s = t` (extensionality) |
| SET 5 | `exists x . (x : s) => choice(s) : s` |

Note: SET 6 (`infinite(BIG)`) is not currently used.

---

## Equality Rules (B-Book Section 1.4)

Referenced by PP spec Chapter 9 (Predicate Prover with Equality).

| Property | Formulation |
|----------|-------------|
| Reflexivity | `E = E` |
| Commutativity | `(E = F) <=> (F = E)` |
| Leibniz's Law | `(E = F) => ([x := E]P <=> [x := F]P)` |
| One-Point Rule | `forall x . (x = E => P) <=> [x := E]P` (if x not free in E) |

---

## Operator Precedence (B-Book Section 1.2)

Referenced by PP spec Chapter 4 (Syntax).

Decreasing priority: `.` `[x:=E]` `not` `&` `or` `=>` `<=>`

---

## Set-Theoretic Constructs Translated by the Set Translator

The Set Translator (spec_pp.md Chapter 3) translates these B-Book
constructs to first-order predicate calculus. The translation
rules (CO, AX, DF, RL, FN, BL, PR, CP) are fully specified in
spec_pp.md Section 3.3. The key B-Book constructs handled are:

- Ordered pairs: `(E, F)`, equality of pairs
- Set membership: `E : s`
- Basic sets: `s x t`, `P(s)`, comprehension `{x | x : s & P}`
- Set operations: union, intersection, difference, singleton
- Relations: inverse, domain, range, composition, identity,
  restrictions, subtraction, image, override, direct product,
  projections, parallel product
- Functions: partial/total functions, injections, surjections,
  bijections, application `f(E)`, lambda abstraction
- Booleans: `BL1`-`BL8`
- Projectors: `PR1`-`PR4`

Constructs NOT handled: trees (B-Book Chapter 3).
