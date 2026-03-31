# Predicate Prover - Specification and Design

**Atelier B**

Document: Predicate Prover - Specification - Design
Date: 05/05/1999
Reference: SM-TEN-B/PSC-D027/1.4

## Authors and Review

| Role | Name | Function/Company |
|------|------|-----------------|
| **Authors** | Jean-Raymond Abrial | Consultant |
| | Nicolas Carré | Engineer |
| **Review** | Bernard Benoit | Quality Manager |
| | Thierry Lecomte | Engineer |
| **Approval** | Thierry Servat | Project Manager |
| **Distribution** | Jean Caire | RATP |
| | B team (Project Binder) | STERIA |

## Version History

| Version | Date | Description |
|---------|------|-------------|
| 1.0 | 16/12/1996 | Document creation |
| 1.1 | 03/12/1997 | Specification update |
| 1.2 | 19/12/1997 | Corrections following acceptance testing |
| 1.3 | 17/03/1999 | Corrections for PP6.1 |
| 1.4 | 05/05/1999 | Corrections for PP6.1.1 |

## Modification History

| Version | Location | Nature of modification |
|---------|----------|----------------------|
| 1.1 | Addition of chapter | The Set Translator |
| 1.2 | pp. 10, 22 | Corrections to the specification |
| 1.3 | | Corrections to certain rules in PP6.1 |
| 1.4 | | Corrections to certain rules in PP6.1.1 |

---

## Table of Contents

- [1 Introduction](#1-introduction)
- [2 Reference Documents](#2-reference-documents)
- [3 The Set Translator](#3-the-set-translator)
  - [3.1 Introduction](#31-introduction)
  - [3.2 Technical Preliminaries](#32-technical-preliminaries)
  - [3.3 Rule Base for Translation](#33-rule-base-for-translation)
  - [3.4 Introduction of Special Hypotheses](#34-introduction-of-special-hypotheses)
  - [3.5 Extension of the Set Translator](#35-extension-of-the-set-translator)
- [4 Syntax](#4-syntax)
- [5 Organisation](#5-organisation)
- [6 Proof and Inference Rules](#6-proof-and-inference-rules)
- [7 Proposition Prover](#7-proposition-prover)
  - [7.1 Syntax](#71-syntax)
  - [7.2 Inference Rules](#72-inference-rules)
  - [7.3 Tactic](#73-tactic)
  - [7.4 Proof Invariant](#74-proof-invariant)
  - [7.5 Optimisation](#75-optimisation)
  - [7.6 New Tactic](#76-new-tactic)
- [8 Predicate Prover](#8-predicate-prover)
  - [8.1 Syntax](#81-syntax)
  - [8.2 Basic Inference Rules](#82-basic-inference-rules)
  - [8.3 Tactic](#83-tactic)
  - [8.4 Proof Invariant](#84-proof-invariant)
  - [8.5 Syntax Extension](#85-syntax-extension)
  - [8.6 Inference Rules for TRUE and FALSE](#86-inference-rules-for-true-and-false)
  - [8.7 Proof Suspension](#87-proof-suspension)
  - [8.8 New Tactic](#88-new-tactic)
  - [8.9 Principle of Universal Hypothesis Instantiation](#89-principle-of-universal-hypothesis-instantiation)
  - [8.10 Normalisation of Universally Quantified Hypotheses](#810-normalisation-of-universally-quantified-hypotheses)
  - [8.11 Inference Rule with Result](#811-inference-rule-with-result)
  - [8.12 Normalisation Mechanism](#812-normalisation-mechanism)
  - [8.13 First Normalisation](#813-first-normalisation)
  - [8.14 Passage from First to Second Normalisation](#814-passage-from-first-to-second-normalisation)
  - [8.15 Passage from Second to Third Normalisation](#815-passage-from-second-to-third-normalisation)
  - [8.16 Discovery of Contradictions on Hypothesis Promotion](#816-discovery-of-contradictions-on-hypothesis-promotion)
  - [8.17 Partial Instantiation of a Universal Hypothesis](#817-partial-instantiation-of-a-universal-hypothesis)
  - [8.18 Unification of Complementary Partial Instantiations](#818-unification-of-complementary-partial-instantiations)
  - [8.19 Searching for Contradiction during the Instantiation Phase](#819-searching-for-contradiction-during-the-instantiation-phase)
  - [8.20 Analysis of the Different Forms of Instantiations](#820-analysis-of-the-different-forms-of-instantiations)
  - [8.21 Simplification of Instantiations](#821-simplification-of-instantiations)
  - [8.22 Final Algorithm for Universal Hypothesis Instantiation](#822-final-algorithm-for-universal-hypothesis-instantiation)
  - [8.23 Particular Instantiations](#823-particular-instantiations)
  - [8.24 New Tactic](#824-new-tactic)
- [9 Predicate Prover with Equality](#9-predicate-prover-with-equality)
  - [9.1 Special Rules due to Reflexivity of Equality](#91-special-rules-due-to-reflexivity-of-equality)
  - [9.2 Special Rules due to Commutativity of Equality](#92-special-rules-due-to-commutativity-of-equality)
  - [9.3 One-Point Rules](#93-one-point-rules)
  - [9.4 Contradictions due to Equalities](#94-contradictions-due-to-equalities)
  - [9.5 New Tactic](#95-new-tactic)
- [10 Extension of the Predicate Prover](#10-extension-of-the-predicate-prover)
  - [10.1 Nature of Arithmetic Predicates](#101-nature-of-arithmetic-predicates)
  - [10.2 Launching Arithmetic or Equality Processing](#102-launching-arithmetic-or-equality-processing)
  - [10.3 Impact of Arithmetic Hypothesis Processing on PP](#103-impact-of-arithmetic-hypothesis-processing-on-pp)
  - [10.4 Miscellaneous Improvements](#104-miscellaneous-improvements)
- [Appendix A: Summary of Rules Used](#appendix-a-summary-of-rules-used)

---

## 1 Introduction

This document corresponds to the specification and design
documentation for the predicate prover V6.1.1.

The predicate prover is an automatic proof program for
formulas of the first-order predicate calculus with
equality. It can be coupled with a front-end intended to
translate set-theoretic formulas into first-order predicates
with equality.

This front-end is presented in Chapter 3.

The syntax specific to the predicate prover is detailed in
Chapter 4.

The layered organisation of the predicate prover is
presented in Chapter 5.

After a brief reminder of proof by inference rules (Chapter
6), we then describe:

- the proposition prover (Chapter 7),
- the predicate prover (Chapter 8),
- the predicate prover with equality (Chapter 9).

The differences between versions V6.0 and V6.1.1 of the
predicate prover are as follows:

- Rule AEN6, which used an incorrect value of MAXINT, has
  been corrected.
- Rules ST10 and ST32 have been protected against wildcard
  cases.
- Rule ST27 has been corrected for the case where n < 0.
- Rules ST34 to ST36 have been moved into the B source to be
  applied appropriately.
- The axiomatisation of integer division has been corrected
  to handle negative integers.
- The two incorrect simplification rules for integer
  division (DIV1 and DIV2) have been removed.
- The discovery of equalities has been enriched by adding 4
  rules (AR5_2 to AR8_2).
- A new rule has been added to handle expressions of the
  form (a ≤ 0) (AR13).
- The use of the solver in normalisation rules has been
  supplemented with two additional rules (NRM29_1 and
  NRM30_1).

## 2 Reference Documents

| Reference | Title |
|-----------|-------|
| Doc[1] | J-R Abrial, *The B-Book*, Cambridge University Press, ISBN 0-521-49619-5 |

## 3 The Set Translator

### 3.1 Introduction

The Set Translator is a program capable of transforming the
statement of a conjecture written in set-theoretic language
into an equivalent conjecture written in the language of the
first-order predicate calculus with equality. This latter
conjecture can then be submitted as-is to the Predicate
Prover, which may succeed in proving it.

The proposed translation is carried out by applying a
certain number of **rewriting rules** (see definition in the
following section), which we will describe below (Section
3.3) in the form of a certain **Rule Base**. After applying
these rules (until exhaustion) to a given statement, we can
say that, as a first approximation, the resulting statement
no longer contains any set-theoretic operator **except the
membership operator**, which however has **no particular
meaning** for the predicate calculus proper.

The set-theoretic expressions that can be translated were
initially limited to elementary expressions of set theory,
relations, and functions (Chapter 2 of Doc[1]). They have
been extended to numerical expressions as well as those
involving sequences. However, trees (Chapter 3 of Doc[1])
are not yet handled.

### 3.2 Technical Preliminaries

In this section, we present a number of general mechanisms
(often of a purely syntactic nature) that will allow us to
describe and carry out the translation process.

#### 3.2.1 Presentation of the Form of Rules

The rewriting rules proposed in Section 3.3 are organised,
as we shall see, into different categories. In each
category, the rules are presented in tables whose general
form is as follows:

| Rule | Left-Hand Side | Right-Hand Side | Remark |
|------|---------------|-----------------|--------|
| ... | ... | ... | ... |

Each rule corresponds to a row of the preceding table. The
first column contains the name of the rule. The left and
right-hand sides of each rule are specified in the following
two columns. Finally, the last column, optional, contains
possible references to particular remarks, which are
specified further on.

A rewriting rule is always assumed to be applied **from left
to right**. In other words, if a sub-formula F of a
statement E **coincides** (see definition below) with the
**pattern** (see definition below) represented by the left-
hand side of a rule R, the application of R to E consists of
replacing the sub-formula F by the corresponding
**instantiation** (see definition below) of the pattern
represented by the right-hand side of R. When several sub-
formulas of E coincide with the left-hand side of a given
rule, the sub-formula located **furthest to the right** in E
is chosen.

A pattern is any formula containing **wildcards**. A
wildcard is, by convention, a simple letter (lowercase or
uppercase).

By definition, we say that a pattern P coincides with a
formula F if we are able to associate a certain formula
(which we call its **instantiation**) to each wildcard
appearing in P, in such a way that, after having replaced
all occurrences of the wildcards in P by the corresponding
instantiations, we obtain exactly the formula F (note that
multiple occurrences of the same wildcard in the pattern P
must obviously be instantiated in the same way).

To apply a rule R to a statement E, whose left-hand side
coincides with a sub-formula F of E, we must first replace
the occurrences of the wildcards in the right-hand side of R
by the instantiations determined by this coincidence: we
thus obtain a certain formula G. We then replace F by G in
E. The formula obtained then corresponds, by definition, to
the application of the rule R to the statement E.

For example, the rule

| Rule | Left-Hand Side | Right-Hand Side |
|------|---------------|-----------------|
| R | (x, y) = (a, b) | (x = a) ∧ (y = b) |

can be applied to the statement

((F1, F2) = (E1, E2)) ⇔ ((E1, E2) = (F1, F2))

since the left-hand side of R, i.e. (x, y) = (a, b),
coincides with the sub-formula (E1, E2) = (F1, F2) of this
statement: the wildcards x, y, a and b of this left-hand
side can be associated respectively with the formulas E1,
E2, F1 and F2. Note that this left-hand side also coincides
with the sub-formula (F1, F2) = (E1, E2), but the former is
located further to the right than the latter in the proposed
statement.

We then obtain the following formula by replacing the sub-
formula (E1, E2) = (F1, F2) of the preceding statement by
the formula (E1 = F1) ∧ (E2 = F2), itself obtained by
replacing in the right-hand side of R, i.e. (x = a) ∧ (y =
b), the wildcards x, y, a and b by the previously determined
instantiations E1, E2, F1 and F2:

((F1, F2) = (E1, E2)) ⇔ ((E1 = F1) ∧ (E2 = F2))

We can apply rule R again to this new statement since the
left-hand side of R now unambiguously coincides with the
sub-formula (F1, F2) = (E1, E2). We obtain the final
formula:

((F1 = E1) ∧ (F2 = E2)) ⇔ ((E1 = F1) ∧ (E2 = F2))

It may of course happen that several rules are
simultaneously applicable. To avoid any ambiguity in the way
translation can proceed, we will therefore specify the order
in which rules must be applied. This order constitutes the
**tactic** of the rule base defining the translation.

#### 3.2.2 Notion of Type and Super-type

The notion of **type** of a set-theoretic expression, which
we will use in what follows, is exactly that defined in
Doc[1] in Chapter 2. Given a set-theoretic expression E, we
therefore consider its type, type(E), which can be, let us
recall, of one of the following three syntactic forms:

```
Type ::= Type x Type
       | P(Type)
       | Base Type
```

We assume that all formulas we are going to translate with
the Set Translator are **correctly typed**. Furthermore, we
assume that these formulas are also **delta-correct**. For
example, given a partial function f and an expression E, we
assume that the use of the expression f(E) always occurs in
a context where it has been possible to prove that E indeed
belongs to the domain of the function f.

When an expression E is of set type (second syntactic
alternative considered above), i.e. its type has the
following form (for a certain type T):

type(E) = P(T)

then the type T in question is called the **super-type** of
E and is denoted:

super(E) = T

When the super-type is defined, we always have:

type(E) = P(super(E))

#### 3.2.3 Notion of Scale

When the type of an expression is a Cartesian product (first
syntactic alternative considered in the preceding section),
we say that this expression is a **compound expression** (in
fact, it is a pair). Such an expression poses a translation
problem when its components (the elements of the pair) are
not made explicit. For example, suppose we have the
following context:

```
f : s --> (t x u)
x : s
y : t
z : u
```

It is clear that the type of the expression f(x) is t x u.
In other words, f(x) is indeed a compound expression.
However, the two components of f(x) do not appear explicitly
in this expression. Conversely, in the expression (y, z),
which is also a compound expression (of the same type as the
previous one), the two components, namely y and z, appear
explicitly.

When the components of a compound expression are not made
explicit, certain proofs performed by the Predicate Prover
may fail; this is why it is important to make explicit the
components of all compound expressions that may be
encountered during the translation process. Note that a
component of a compound expression may itself be a compound
expression, etc.

The two operators used to make the components of a compound
expression explicit are **pj1** and **pj2**. These two
operators (introduced solely by the Set Translator) should
not be confused with the two mathematical functions prj1(s,
t) and prj2(s, t), which are part of the set-theoretic
language and which, as such, are translated by the Set
Translator. For example, in the case at hand, the expression
f(x) will be systematically translated to:

(pj1(f(x)), pj2(f(x)))

To be able to easily generate the components (or sub-
components) of a compound expression, we introduce the
notion of **scale**. The scale of an expression is a
simplification of its type. We therefore first define the
syntactic operator **echt** acting on the different forms of
types as indicated by the rewriting rules presented in the
table below, a table that should be considered in decreasing
priority order of its successive rows:

| Left-Hand Side | Right-Hand Side |
|---------------|-----------------|
| echt(s x t) | (echt(s), echt(t)) |
| echt(P(s)) | * |
| echt(s) | * |

For example, we have:

echt((s x t) x (s x (t x u))) = ((*, *), (*, (*, *)))

By extension, the scale, denoted eche(E), of a certain
expression E, is the scale echt of its type. That is, by
definition:

eche(E) =def echt(type(E))

For example, for the expression f(x) considered previously,
we have:

```
eche(f(x)) = echt(type(f(x)))
           = echt(t x u)
           = (*, *)
```

#### 3.2.4 Decomposition of a Compound Expression

To decompose a compound expression, we use the syntactic
operator **dcp** taking as arguments the expression in
question and its scale. This construction is then reduced by
the rewriting rules presented in the table below, which,
like the previous one, should be used in decreasing priority
order of its rows.

| Left-Hand Side | Right-Hand Side |
|---------------|-----------------|
| dcp((E, F), (u, v)) | (dcp(E, u), dcp(F, v)) |
| dcp(E, (u, v)) | (dcp(pj1(E), u), dcp(pj2(E), v)) |
| dcp(E, *) | E |

For example, to decompose the compound expression f(x)
considered above, we first form its scale from its type,
which gives, as we have seen, (*, *). We then perform the
reduction of the construction dcp(f(x), (*, *)):

```
dcp(f(x), (*, *))
  = (dcp(pj1(f(x)), *), dcp(pj2(f(x)), *))
  = (pj1(f(x)), pj2(f(x)))
```

#### 3.2.5 Quantification over Compound Variables

The notion of scale is also used to construct the quantified
variables entering into the translation of certain set-
theoretic formulas. For example, the formula
s ⊆ t is translated, as we shall see, by the predicate:

∀ x · (x ∈ s ⇒ x ∈ t)

In fact, when the sets s and t have a super-type
(necessarily common if the typing is correct) that
corresponds to a Cartesian product, we decompose the
variable x into a structured variable that follows the shape
of this Cartesian product. For example, if the sets s and t
become respectively a x (b x c) and d x (e x f), the naive
translation:

∀ x · (x ∈ a x (b x c) ⇒ x ∈ d x (e x f))

is not suitable because it does not allow the Predicate
Prover to work under good conditions. We would need instead
the more elaborate translation:

∀ (x1, x2, x3) · ((x1, (x2, x3)) ∈ a x (b x c) ⇒ (x1, (x2, x3)) ∈ d x (e x f))

which can itself be further translated to give the final
predicate:

∀ (x1, x2, x3) · (x1 ∈ a ∧ x2 ∈ b ∧ x3 ∈ c ⇒ x1 ∈ d ∧ x2 ∈ e ∧ x3 ∈ f)

To carry out the translation of s ⊆ t when the super-type of
s is a Cartesian product as in the case a x (b x c) ⊆ d x (e
x f), we consider the scale associated with this super-type:

echt(super(a x (b x c))) = (*, (*, *))

We must then **paint** this scale with as many **fresh
variables** as there are occurrences of the symbol *. We
define for this the syntactic operator **paint**. We get:

paint(*, (*, *)) = (x1, (x2, x3))

It then remains to replace x by this last formula in the
preceding predicate. We get:

∀ (x1, (x2, x3)) · ((x1, (x2, x3)) ∈ a x (b x c) ⇒ (x1, (x2, x3)) ∈ d x (e x f))

The translation is not yet finished. It remains to
**flatten** the definition of the variables located just
after the quantifier, i.e. to replace the first occurrence
of (x1, (x2, x3)) by (x1, x2, x3). We define for this the
syntactic operator **flatten**. We therefore have:

flatten(x1, (x2, x3)) = (x1, x2, x3)

This done, we obtain the final translation:

∀ (x1, x2, x3) · ((x1, (x2, x3)) ∈ a x (b x c) ⇒ (x1, (x2, x3)) ∈ d x (e x f))

In summary, the complete translation of the predicate s ⊆ t
can be written:

∀ X · (V ∈ s ⇒ V ∈ t)

where X and V are defined as:

- X =def flatten(V)
- V =def paint(echt(super(s)))

We will not further define in this document the two
syntactic operators **paint** and **flatten**.

### 3.3 Rule Base for Translation

The rewriting rules we now present are grouped under
different categories:

- Rules concerning the equality of ordered pairs.
- Rules concerning the axioms of set theory.
- Rules concerning elementary set-theoretic definitions.
- Rules concerning relational operators.
- Rules concerning functional operators.
- Rules concerning Boolean expressions.
- Rules concerning projectors.
- Rules concerning the decomposition of compound
  expressions.

#### 3.3.1 Rules Concerning the Equality of Ordered Pairs

| Rule | Left-Hand Side | Right-Hand Side |
|------|---------------|-----------------|
| CO1 | (x, y) = (a, b) | (x = a) ∧ (y = b) |
| CO2 | (x ↦ y) = (a, b) | (x = a) ∧ (y = b) |
| CO3 | (x, y) = (a ↦ b) | (x = a) ∧ (y = b) |
| CO4 | (x ↦ y) = (a ↦ b) | (x = a) ∧ (y = b) |

#### 3.3.2 Rules Concerning the Axioms of Set Theory

| Rule | Left-Hand Side | Right-Hand Side | Remark |
|------|---------------|-----------------|--------|
| AX1 | (E, F) ∈ s × t | E ∈ s ∧ F ∈ t | |
| AX2 | s ∈ P(t) | ∀ X · (V ∈ s ⇒ V ∈ t) | (1) |
| AX3 | E ∈ SET x · P | Q | (2) |
| AX21 | s ⊆ t | s ∈ P(t) | |
| AX22 | s ⊂ t | s ∈ P(t) ∧ ¬(s = t) | |
| AX31 | E ∈ {x \| P} | E ∈ SET x · P | |

**Remarks:**

(1) X =def flatten(V); V =def paint(echt(super(s))); X is
not free in s and t

(2) Q =def [x := E] P

#### 3.3.3 Rules Concerning Elementary Set-Theoretic Definitions

| Rule | Left-Hand Side | Right-Hand Side | Remark |
|------|---------------|-----------------|--------|
| DF1 | E ∈ ∩ x · (P \| F) | ∀ x · (P ⇒ E ∈ F) | (1) |
| DF2 | E ∈ ∪ x · (P \| F) | ∃ x · (P ∧ E ∈ F) | (1) |
| DF3 | E ∈ inter(s) | ∀ X · (V ∈ s ⇒ E ∈ V) | (2) |
| DF4 | E ∈ union(s) | ∃ X · (V ∈ s ∧ E ∈ V) | (2) |
| DF5 | s ∈ P1(t) | s ∈ P(t) ∧ ∃ X · (V ∈ s) | (3) |
| DF6 | E ∈ ∅ | FALSE | |
| DF7 | E ∈ {x, y} | E ∈ {x} ∨ E ∈ {y} | |
| DF8 | E ∈ {x} | E = x | (4) |
| DF9 | E ∈ u − v | (E ∈ u) ∧ ¬(E ∈ v) | |
| DF10 | E ∈ u ∩ v | (E ∈ u) ∧ (E ∈ v) | |
| DF11 | E ∈ u ∪ v | (E ∈ u) ∨ (E ∈ v) | |

**Remarks:**

(1) The variable x is not free in E.

(2) X =def flatten(V); V =def paint(echt(super(s))); X is
not free in s and E

(3) X =def flatten(V); V =def paint(echt(super(s))); X is
not free in s and t

(4) x is not the definition of a set in comprehension

#### 3.3.4 Rules Concerning Relational Operators

| Rule | Left-Hand Side | Right-Hand Side | Remark |
|------|---------------|-----------------|--------|
| RL1 | r ∈ s ↔ t | dom(r) ⊆ s ∧ ran(r) ⊆ t | |
| RL2 | ((E, F), (G, H)) ∈ (f \|\| g) | (E, G) ∈ f ∧ (F, H) ∈ g | |
| RL3 | ((E, F), G) ∈ prj1(s, t) | (E ∈ s) ∧ (F ∈ t) ∧ (G = E) | |
| RL4 | ((E, F), G) ∈ prj2(s, t) | (E ∈ s) ∧ (F ∈ t) ∧ (G = F) | |
| RL5 | (E, (F, G)) ∈ f ⊗ g | (E, F) ∈ f ∧ (E, G) ∈ g | |
| RL6 | (E, F) ∈ (q <+ r) | (E, F) ∈ r ∨ (E, F) ∈ (dom(r) ◁ q) | |
| RL7 | F ∈ r[w] | ∃ X · (V ∈ w ∧ (V, F) ∈ r) | (1) |
| RL8 | (E, F) ∈ (r ▷ v) | (E, F) ∈ r ∧ ¬(F ∈ v) | |
| RL9 | (E, F) ∈ (u ◁ r) | (E, F) ∈ r ∧ ¬(E ∈ u) | |
| RL10 | (E, F) ∈ (r ▷ v) | (E, F) ∈ r ∧ F ∈ v | |
| RL11 | (E, F) ∈ (u ◁ r) | (E, F) ∈ r ∧ E ∈ u | |
| RL12 | (E, F) ∈ id(s) | (E ∈ s) ∧ (E = F) | |
| RL13 | (E, F) ∈ (p ; q) | ∃ X · ((E, V) ∈ p ∧ (V, F) ∈ q) | (2) |
| RL14 | F ∈ ran(r) | ∃ X · (V, F) ∈ r | (3) |
| RL15 | E ∈ dom(r) | ∃ X · (E, V) ∈ r | (4) |
| RL16 | (E, F) ∈ r−1 | (F, E) ∈ r | |

**Remarks:**

(1) X =def flatten(V); V =def paint(echt(super(dom(r)))); X
is not free in F, R and w

(2) X =def flatten(V); V =def paint(echt(super(ran(p)))); X
is not free in E, F, p and q

(3) X =def flatten(V); V =def paint(echt(super(ran(r)))); X
is not free in E and r

(4) X =def flatten(V); V =def paint(echt(super(dom(r)))); X
is not free in F and r

#### 3.3.5 Rules Concerning Functional Operators

| Rule | Left-Hand Side | Right-Hand Side | Remark |
|------|---------------|-----------------|--------|
| FN1 | f ∈ s ↣t | f ∈ s ↠ t ∧ func(f−1, t, s) | |
| FN2 | f ∈ s ↣ t | f ∈ s ↠ t ∧ func(f−1, t, s) | |
| FN3 | f ∈ s ↠ t | f ∈ s → t ∧ t ⊆ ran(f) | |
| FN4 | f ∈ s ↠ t | f ∈ s → t ∧ t ⊆ ran(f) | |
| FN5 | f ∈ s ↣ t | f ∈ s → t ∧ func(f−1, t, s) | |
| FN6 | f ∈ s ↣ t | f ∈ s → t ∧ func(f−1, t, s) | |
| FN7 | f ∈ s → t | f ∈ s → t ∧ s ⊆ dom(f) | |
| FN8 | f ∈ s → t | f ∈ s ↔ t ∧ func(f, s, t) | |
| FN9 | func(f, s, t) | ∀ X · ((A, B) ∈ f ∧ (A, C) ∈ f ⇒ B = C) | (1) |
| FN10 | (E, F) ∈ λ x · (P \| G) | Q ∧ (F = H) | (2) |

**Remarks:**

(1) T =def super(s × t × t); A, B, C =def paint(echt(T)); X =def paint(echt(T));
X is not free in f

(2) Q =def [x := E] P; H =def [x := E] G

#### 3.3.6 Rules Concerning Boolean Expressions

| Rule | Left-Hand Side | Right-Hand Side |
|------|---------------|-----------------|
| BL1 | btrue | TRUE |
| BL2 | bfalse | FALSE |
| BL3 | bool(P) : BOOL | TRUE |
| BL4 | x = bool(P) | P ⇔ (x = 0) |
| BL5 | bool(P) = x | P ⇔ (x = 0) |
| BL6 | BOOL | {0, 1} |
| BL7 | FALSE | 1 |
| BL8 | TRUE | 0 |

#### 3.3.7 Rules Concerning Projectors

| Rule | Left-Hand Side | Right-Hand Side |
|------|---------------|-----------------|
| PR1 | pj2(a ↦ b) | b |
| PR2 | pj1(a ↦ b) | a |
| PR3 | pj2(a, b) | b |
| PR4 | pj1(a, b) | a |

#### 3.3.8 Rules Concerning the Decomposition of Compound Expressions

| Rule | Left-Hand Side | Right-Hand Side | Remark |
|------|---------------|-----------------|--------|
| CP1 | f(E) | f(R) | (1) |
| CP2 | E : s | R : s | (1) |

**Remark:**

(1) R =def dcp(E, echt(type(E)))

#### 3.3.9 Tactic

The rewriting rules presented in the preceding sections are
applied in the following decreasing order:

PR, BL, FN, RL, DF, AX, CO, CP

Within each category, the rules are applied in decreasing
priority order of their appearance in the corresponding
table.

### 3.4 Introduction of Special Hypotheses

When a conjecture C that we propose to translate contains a
sub-formula of the form f(E) (a sub-formula corresponding to
the application of a function f to a certain argument E), we
introduce an additional hypothesis H intended to give
meaning to the said application. In other words, if the
actual translation of C is the predicate P, we generate the
final predicate H ⇒ P.

The additional hypothesis in question is effectively
generated if the type of f is of the form P(S × T), i.e. if
f is (at least) a binary relation. This hypothesis is then:

∀ x · (x, f(x)) ∈ f

It signifies that every pair of the form (x, f(x)) indeed
belongs to the function f understood as a relation (i.e. a
set of pairs). Note that we do not require that, in this
quantification, the variable x belongs to the domain of f,
nor that f is effectively a function. Indeed, these
preconditions are already guaranteed by the fact that the
expression f(E), like any expression encountered in the
conjecture, is assumed to be delta-correct, as we noted in
Section 3.2.2.

### 3.5 Extension of the Set Translator

In this section, we present an extension of the Set
Translator consisting essentially of integrating the
translation of formulas pertaining to integer arithmetic.
This extension then opens the door to other developments
concerning intervals, sequences, and the treatment of the
minimum and maximum operators. We also took the opportunity
to systematise the treatment of equality.

This extension is coherent with that performed on the
Predicate Prover (described in the remainder of this
document) to include the treatment of integer arithmetic.

The use of the rules presented below assumes that the lemma
submitted for translation has successfully passed **type
checking** and that it contains no expression that is
meaningless.

#### 3.5.1 Normalisation of Arithmetic Predicates

The following rules systematically transform all arithmetic
predicates into normalised predicates of the form E ≤ 0,
where E is an integer arithmetic expression constructed from
the operators +, − (binary and unary), ×, / and mod. These
last two operators will be axiomatised (see below).

| Rule | Left-Hand Side | Right-Hand Side |
|------|---------------|-----------------|
| NPA1 | a ≤ b | a − b ≤ 0 |
| NPA2 | ¬(a ≤ b) | b − a + 1 ≤ 0 |
| NPA3 | a < b | a − b + 1 ≤ 0 |
| NPA4 | ¬(a < b) | b − a ≤ 0 |
| NPA5 | a ≥ b | b − a ≤ 0 |
| NPA6 | ¬(a ≥ b) | a − b + 1 ≤ 0 |
| NPA7 | a > b | b − a + 1 ≤ 0 |
| NPA8 | ¬(a > b) | a − b ≤ 0 |

#### 3.5.2 Rules Defining Membership in Numerical Sets

The following rules translate membership in numerical sets.

| Rule | Left-Hand Side | Right-Hand Side |
|------|---------------|-----------------|
| AEN1 | x ∈ a .. b | a ≤ x ∧ x ≤ b |
| AEN2 | x ∈ INTEGER | TRUE |
| AEN3 | x ∈ NATURAL | n ≥ 0 |
| AEN4 | x ∈ NATURAL1 | n > 0 |
| AEN5 | x ∈ NAT | x ∈ 0 .. 2147483647 |
| AEN6 | x ∈ NAT1 | x ∈ 1 .. 2147483647 |

Rule AEN2 results from the fact that the type checker has
already done its work (recall that INTEGER is one of the
base types).

#### 3.5.3 Rules Defining Membership in Sequences

A sequence u, belonging to the set seq(S), is considered as
a total function from the interval 1 .. size(u) to the set
S. Expressions of the form size(u) are translated
systematically for all sequence expressions (see below).
Irreducible expressions of the form size(u) will not be
interpreted by PP. The rules for membership in sequences are
presented below.

| Rule | Left-Hand Side | Right-Hand Side |
|------|---------------|-----------------|
| ST1 | u ∈ seq(S) | 0 ≤ size(s) ∧ s ∈ (1 .. size(s)) → S |
| ST2 | (i, y) ∈ x → s | i ∈ 1 .. size(s) + 1 ∧ (i = 1 ⇒ y = x) ∧ (i ∈ 2 .. size(s) + 1 ⇒ (i − 1, y) ∈ s) |
| ST3 | (i, y) ∈ s ← x | i ∈ 1 .. size(s) + 1 ∧ (i = size(s) + 1 ⇒ y = x) ∧ (i ∈ 1 .. size(s) + 1 ⇒ (i, y) ∈ s) |
| ST4 | (i, y) ∈ front(s) | i ∈ 1 .. size(s) − 1 ∧ (i, y) ∈ s |
| ST5 | (i, y) ∈ tail(s) | i ∈ 1 .. size(s) − 1 ∧ (i + 1, y) ∈ s |
| ST6 | (i, y) ∈ s ⌢ t | i ∈ 1 .. size(s) + size(t) ∧ (i ∈ 1 .. size(s) ⇒ (i, y) ∈ s) ∧ (i ∈ size(s) + 1 .. size(s) + size(t) ⇒ (i − size(s), y) ∈ t) |
| ST7 | (i, y) ∈ rev(s) | i ∈ 1 .. size(s) ∧ (size(s) − i + 1, y) ∈ s |
| ST8 | (i, y) ∈ s ↑ n | n ∈ 0 .. size(s) ∧ i ∈ 1 .. n ∧ (i, y) ∈ s |
| ST9 | (i, y) ∈ s ↓ n | n ∈ 0 .. size(s) ∧ i ∈ 1 .. size(s) − n ∧ (i + n, y) ∈ s |
| ST10 | (i, b) ∈ [x] | (i, b) ∈ ∅ ← x | (1) |
| ST11 | (i, b) ∈ [a, x] | (i, b) ∈ [a] ← x | |

**Remark:** (1) x must not be of the form (a, b); x must not
be a wildcard

#### 3.5.4 Rules Defining Sequence Indexing

The rules for expressions of the form s(i) when s is a
sequence are presented below.

| Rule | Left-Hand Side | Right-Hand Side |
|------|---------------|-----------------|
| ST12 | first(s) | s(1) |
| ST13 | last(s) | s(size(s)) |
| ST14 | R((x → s)(i)) | (i = 1 ⇒ R(x)) ∧ (i ∈ 2 .. size(s) + 1 ⇒ R(s(i − 1))) |
| ST15 | R((s ← x)(i)) | (i = size(s) + 1 ⇒ R(x)) ∧ (i ∈ 1 .. size(s) ⇒ R(s(i))) |
| ST16 | front(s)(i) | s(i) |
| ST17 | tail(s)(i) | s(i + 1) |
| ST18 | R((s ⌢ t)(i)) | (i ∈ 1 .. size(s) ⇒ R(s(i))) ∧ (i ∈ size(s) + 1 .. size(s) + size(t) ⇒ R(t(i − size(s)))) |
| ST19 | rev(s)(i) | s(size(s) − i + 1) |
| ST20 | (s ↑ n)(i) | s(i) |
| ST21 | (s ↓ n)(i) | s(i + n) |

Note that rules ST14, ST15 and ST18 generate conditional
expressions. These conditions are brought out to the highest
level by means of the conjunction of two implicative
predicates. It is necessary, of course, for the indexing
expressions in question not to be located inside a
quantification.

#### 3.5.5 Rules Defining Sequence Size

| Rule | Left-Hand Side | Right-Hand Side | Remark |
|------|---------------|-----------------|--------|
| ST22 | size(x → s) | size(s) + 1 | |
| ST23 | size(s ← x) | size(s) + 1 | |
| ST24 | size(front(s)) | size(s) − 1 | |
| ST25 | size(tail(s)) | size(s) − 1 | |
| ST26 | size(∅) | 0 | |
| ST27 | R(size(id(1 .. n))) | (n ≥ 0 ⇒ R(n)) ∧ (n < 0 ⇒ R(0)) | |
| ST28 | size(s ⌢ t) | size(s) + size(t) | |
| ST29 | size(rev(s)) | size(s) | |
| ST30 | size(s ↑ n) | n | |
| ST31 | size(s ↓ n) | size(s) − n | |
| ST32 | size([a]) | 1 | (1) |
| ST33 | size([a, x]) | size([a]) + 1 | |
| ST34 | R(size(s ; f)) | (ran(s) ⊆ dom(f) ⇒ R(size(s))) ∧ ran(s) ⊆ dom(f) | |
| ST35 | R(size(s <+ f)) | (dom(f) ⊆ dom(s) ⇒ R(size(s))) ∧ dom(f) ⊆ dom(s) | |
| ST36 | R(size(s ⊗ f)) | (dom(f) = dom(s) ⇒ R(size(s))) ∧ dom(f) = dom(s) | |

**Remark:** (1) a must not be of the form (x, y); a must not
be a wildcard

The last rules define conditional expressions (see above).

#### 3.5.6 Rules Defining the min and max Operators

The following rules define the rules for the min and max
operators when they are involved in comparisons. We will
consider the other cases below.

| Rule | Left-Hand Side | Right-Hand Side |
|------|---------------|-----------------|
| MIN1 | min({a, b}) ≤ p | min({a}) ≤ p ∨ b ≤ p |
| MIN2 | min({a}) ≤ p | a ≤ p |
| MIN3 | min(a ∪ b) ≤ p | min(a) ≤ p ∨ min(b) ≤ p |
| MIN4 | min(s) ≤ p | ∃ x · (x ∈ s ∧ x ≤ p) |
| MIN5 | p ≤ min({a, b}) | p ≤ min({a}) ∧ p ≤ b |
| MIN6 | p ≤ min({a}) | p ≤ a |
| MIN7 | p ≤ min(a ∪ b) | p ≤ min(a) ∧ p ≤ min(b) |
| MIN8 | p ≤ min(s) | ∀ x · (x ∈ s ⇒ p ≤ x) |
| MAX1 | max({a, b}) ≤ p | max({a}) ≤ p ∧ b ≤ p |
| MAX2 | max({a}) ≤ p | a ≤ p |
| MAX3 | max(a ∪ b) ≤ p | max(a) ≤ p ∧ max(b) ≤ p |
| MAX4 | max(s) ≤ p | ∀ x · (x ∈ s ⇒ x ≤ p) |
| MAX5 | p ≤ max({a, b}) | p ≤ max({a}) ∨ p ≤ b |
| MAX6 | p ≤ max({a}) | p ≤ a |
| MAX7 | p ≤ max(a ∪ b) | p ≤ max(a) ∨ p ≤ max(b) |
| MAX8 | p ≤ max(s) | ∃ x · (x ∈ s ∧ p ≤ x) |

#### 3.5.7 Translation of Equality

We present below a number of rules relating to equality.
Indeed, the translation of an equality expression depends on
the type of the expressions involved.

| Rule | Left-Hand Side | Right-Hand Side | Type and Condition |
|------|---------------|-----------------|-------------------|
| EQL1 | −a = 0 | a = 0 | integer |
| EQL2 | a × b = 0 | a = 0 ∨ b = 0 | integer |
| EQL3 | a = 0 | a ≤ 0 ∧ 0 ≤ a | integer |
| EQL4 | a = b | a − b = 0 | integer |
| EQL51 | s = t | s ⊆ t ∧ t ⊆ s ∧ eql_set(s, t) | set; s is a variable |
| EQL52 | s = t | s ⊆ t ∧ t ⊆ s ∧ eql_set(t, s) | set; t is a variable |
| EQL6 | s = t | s ⊆ t ∧ t ⊆ s | set |
| EQL7 | s = ∅ | s ⊆ ∅ | set |

#### 3.5.8 Direct Axiomatisation of Integer Division and Modulo

Arithmetic expressions of the form a/b are axiomatised
directly. a denotes an integer expression, while b denotes a
non-zero integer expression. Each expression of the form a/b
is replaced by a constant c, which assumes that the
expressions a/b under consideration do not depend on
quantified variables.

Then each of these constants c is axiomatised. The axioms in
question are added as additional hypotheses to the
translated lemma. The axiomatisation is as follows:

- a ≥ 0 ∧ b > 0 ⇒ 0 ≤ c ∧ b × c ≤ a ∧ a < b × (c + 1)
- a ≥ 0 ∧ b < 0 ⇒ c ≤ 0 ∧ −b × −c ≤ a ∧ a < −b × (−c + 1)
- a < 0 ∧ b > 0 ⇒ c ≤ 0 ∧ b × −c ≤ −a ∧ −a < b × (−c + 1)
- a < 0 ∧ b < 0 ⇒ 0 ≤ c ∧ a ≤ b × c ∧ b × (c + 1) < a

The modulo operator is defined by the following rule:

| Rule | Left-Hand Side | Right-Hand Side |
|------|---------------|-----------------|
| MOD1 | a mod b | a − b × (a / b) |

#### 3.5.9 Direct Axiomatisation of min and max

The rules given above do not cover all expressions
containing the min or max operators. In those cases, we use
a direct axiomatisation similar to that described above for
integer division. Each of the concerned expressions is
replaced by a constant c whose axiomatisation is added to
the hypotheses of the translated lemma.

The axiomatisation for min(s) is:

c ∈ s ∧ ∀ x · (x ∈ s ⇒ c ≤ x)

The axiomatisation for max(s) is:

c ∈ s ∧ ∀ x · (x ∈ s ⇒ x ≤ c)

Particular axiomatisations have also been proposed when the
set s is defined in extension.

---

## 4 Syntax

The formulas that can be submitted to the predicate prover
follow the syntax:

```
prd ::= prd ∧ prd
      | prd ∨ prd
      | prd ⇒ prd
      | prd ⇔ prd
      | ¬ prd
      | ∀ vrb · prd
      | ∃ vrb · prd
      | exp = exp
      | frm

vrb ::= vrb, idt
      | idt
```

The symbols `frm` and `exp` denote respectively predicates
and expressions corresponding to formulas of an extended
syntax (formulas containing, of course, none of the logical
connectives of the preceding syntax). These syntactic forms
serve to write arbitrary predicates or expressions. The
symbol `idt` denotes an identifier formed of one or more
letters.

The operators introduced in the preceding syntax obey the
following (relative) priority and associativity rules:

| Operator | Priority | Associativity | ASCII |
|----------|----------|---------------|-------|
| · | 7 | right | `.` |
| ∀ | 6 | | `!` |
| ∃ | 6 | | `#` |
| , | 5 | left | `,` |
| = | 4 | left | `=` |
| ¬ | 3 | | `not` |
| ∧ | 2 | left | `and` |
| ∨ | 2 | left | `or` |
| ⇒ | 0 | left | `=>` |
| ⇔ | 1 | left | `<=>` |
| ♢ | 11 | | `forall` |
| ♡ | 11 | | `forall2` |

Note that it is always possible to place sub-formulas in
parentheses to override the preceding rules.

In the syntax, operators have been presented in their
mathematical form, which is what we will use in this
document. To implement the predicate prover, one uses the
ASCII form shown in the last column of the preceding table.

## 5 Organisation

The predicate prover is organised as a series of three
provers nested within one another:

- the **proposition prover**, which constitutes a decision
  procedure for propositional calculus,
- the **predicate prover** proper, which extends the
  preceding to first-order predicate calculus,
- the **equality prover**, which extends the preceding to
  account for equality.

Our presentation will follow this organisation.

## 6 Proof and Inference Rules

The provers presented in this document will be defined using
inference rules. We refer to Doc[1] (Chapter 1) for more
details on the nature of these rules and on how to use them
in backward chaining to carry out proofs mechanically.

Let us recall here only that inference rules follow the
general form:

```
  Σ₁
  .
  .
  .
  Σₙ
  ──
  Σ
```

where the Σᵢ are **sequents**, i.e. constructions of the
form

H ⊢ P

where H denotes a finite collection of predicates
constituting the hypotheses of the sequent, and where P
denotes a predicate constituting the conclusion of the
sequent.

The sequents Σ₁, ..., Σₙ constitute the **antecedents** of
the preceding rule, while Σ constitutes its **consequent**.
Most of the time the number of antecedents is equal to 1,
sometimes 2. It can also be zero, in which case the rule is
called an **axiom**.

In what follows, we will represent a rule named R by a table
as indicated below:

| R | Antecedents | Consequent |
|---|-------------|------------|
| | Σ₁ ... Σₙ | Σ |

Note that sometimes certain antecedents are not sequents,
but rather **side conditions** which are simply written in
plain language. We will later extend the notion of inference
rule presented here to that of an inference rule said to be
**with result** (Section 8.11).

---

## 7 Proposition Prover

### 7.1 Syntax

This prover is capable of deciding the validity of formulas
following the restricted syntax:

```
prp ::= prp ∧ prp
      | prp ∨ prp
      | prp ⇒ prp
      | prp ⇔ prp
      | ¬ prp
      | frm
```

Note that the syntactic category `prp` is a sub-category of
the syntactic category `prd` introduced previously (i.e. any
formula that reduces to `prp` also reduces to `prd`).

### 7.2 Inference Rules

This prover is built from the following six groups of rules:

- the four rules related to conjunction (AND),
- the four rules related to disjunction (OR),
- the four rules related to implication (IMP),
- the four rules related to equivalence (EQV),
- the two rules related to negation (NOT),
- the three axioms (AXM)

The rules of the first four groups all have consequents of
the same form (where the symbol ⊙ corresponds to ∧, ∨, ⇒ or
⇔ respectively):

| | Antecedents | Consequent |
|---|-------------|------------|
| 1 | ... | H ⊢ ¬(P ⊙ Q) ⇒ R |
| 2 | ... | H ⊢ ¬(P ⊙ Q) |
| 3 | ... | H ⊢ (P ⊙ Q) ⇒ R |
| 4 | ... | H ⊢ P ⊙ Q |

Here are the rules for conjunction:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| AND1 | H ⊢ ¬Q ⇒ R; H ⊢ ¬P ⇒ R | H ⊢ ¬(P ∧ Q) ⇒ R |
| AND2 | H ⊢ P ⇒ ¬Q | H ⊢ ¬(P ∧ Q) |
| AND3 | H ⊢ P ⇒ (Q ⇒ R) | H ⊢ (P ∧ Q) ⇒ R |
| AND4 | H ⊢ Q; H ⊢ P | H ⊢ P ∧ Q |

Here are the rules for disjunction:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| OR1 | H ⊢ ¬P ⇒ (¬Q ⇒ R) | H ⊢ ¬(P ∨ Q) ⇒ R |
| OR2 | H ⊢ ¬Q; H ⊢ ¬P | H ⊢ ¬(P ∨ Q) |
| OR3 | H ⊢ Q ⇒ R; H ⊢ P ⇒ R | H ⊢ (P ∨ Q) ⇒ R |
| OR4 | H ⊢ ¬P ⇒ Q | H ⊢ P ∨ Q |

One notices certain similarities between the following pairs
of rules: AND1 and OR3, AND2 and OR4, AND3 and OR1, AND4 and
OR2. They arise from the equivalence between ¬(P ∧ Q) and
(¬P ∨ ¬Q).

Here are the rules for implication:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| IMP1 | H ⊢ P ⇒ (¬Q ⇒ R) | H ⊢ ¬(P ⇒ Q) ⇒ R |
| IMP2 | H ⊢ ¬Q; H ⊢ P | H ⊢ ¬(P ⇒ Q) |
| IMP3 | H ⊢ Q ⇒ R; H ⊢ ¬P ⇒ R | H ⊢ (P ⇒ Q) ⇒ R |
| IMP4 | H, P ⊢ Q | H ⊢ P ⇒ Q |

One notices certain similarities between the following pairs
of rules: OR1 and IMP1, OR2 and IMP2, OR3 and IMP3. They
arise from the equivalence between (P ∨
Q) and (¬P ⇒ Q).

Here are the rules for equivalence:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| EQV1 | H ⊢ P ⇒ (¬Q ⇒ R); H ⊢ ¬P ⇒ (Q ⇒ R) | H ⊢ ¬(P ⇔ Q) ⇒ R |
| EQV2 | H ⊢ P ⇒ ¬Q; H ⊢ ¬Q ⇒ P | H ⊢ ¬(P ⇔ Q) |
| EQV3 | H ⊢ P ⇒ (Q ⇒ R); H ⊢ ¬P ⇒ (¬Q ⇒ R) | H ⊢ (P ⇔ Q) ⇒ R |
| EQV4 | H ⊢ P ⇒ Q; H ⊢ Q ⇒ P | H ⊢ P ⇔ Q |

One notices certain similarities between the following pairs
of rules: EQV1 and EQV3, EQV2 and EQV4. They arise from the
equivalence between ¬(P ⇔ Q) and (P ⇔
¬Q).

Here are the two rules for negation:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| NOT1 | H ⊢ P ⇒ R | H ⊢ ¬¬P ⇒ R |
| NOT2 | H ⊢ P | H ⊢ ¬¬P |

One sees immediately that the two rules that could have been
named NOT3 and NOT4, whose consequents would have been H ⊢
¬P ⇒ R and H ⊢ ¬P, need not exist because such consequents
are directly handled by rules AND1, OR1, IMP1, EQV1 for the
first, and by rules AND2, OR2, IMP2, EQV2 for the second.

Here finally are the three axioms:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| AXM1 | ¬P is in H | H ⊢ P ⇒ Q |
| AXM2 | P is in H | H ⊢ ¬P ⇒ Q |
| AXM3 | P is in H | H ⊢ P |

The side conditions appearing in these last three rules have
the following intuitive meaning: "P is in H" means that the
predicate P is one of the hypotheses in the finite
collection of hypotheses H. One could define rules acting on
the collection H that would allow such side conditions to be
fully formalised. However, we feel that this excess of
formalism is unnecessary here.

### 7.3 Tactic

The preceding rules are applied as follows, in decreasing
priority order:

- any of the rules AND, OR, IMP1, IMP2, IMP3, EQV, NOT,
- any of the rules AXM,
- the rule IMP4.

### 7.4 Proof Invariant

It follows from the tactic proposed in the preceding section
that, during the proof, the hypotheses of the current
sequent are constituted only of **simple propositions**:
that is, propositions containing none of the operators ∧, ∨,
⇒ or ⇔ or ¬ (unless the latter is the outermost operator).
This is due to the fact that every consequent of the form

H ⊢ A ⇒ R

where A is not a simple proposition, can be handled by one
of the following rules: AND1, OR1, IMP1, EQV1, NOT1, AND3,
OR3, IMP3, EQV3 (and only by one of them). To be convinced
of this, it suffices to consider all the forms that the
sequent H ⊢ A ⇒ R can take when A is not a simple
proposition and to see which rule is then applicable:

| Sequent | Rule |
|---------|------|
| H ⊢ ¬(P ∧ Q) ⇒ R | AND1 |
| H ⊢ ¬(P ∨ Q) ⇒ R | OR1 |
| H ⊢ ¬(P ⇒ Q) ⇒ R | IMP1 |
| H ⊢ ¬(P ⇔ Q) ⇒ R | EQV1 |
| H ⊢ ¬¬P ⇒ R | NOT1 |
| H ⊢ (P ∧ Q) ⇒ R | AND3 |
| H ⊢ (P ∨ Q) ⇒ R | OR3 |
| H ⊢ (P ⇒ Q) ⇒ R | IMP3 |
| H ⊢ (P ⇔ Q) ⇒ R | EQV3 |

Consequently, rule IMP4, which when applied to the sequent H
⊢ A ⇒ R has the effect of promoting A to a hypothesis, only
does so when A is a simple proposition, since, by virtue of
the tactic considered in Section 7.3, this rule is applied
only when no other can be.

### 7.5 Optimisation

To improve the prover's performance, a number of derived
rules have been added.

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| IMP5 | P is in H; H ⊢ Q | H ⊢ P ⇒ Q |
| AXM4 | R is in H | H ⊢ P ⇒ R |
| AXM5 | ¬Q is in H | H ⊢ P ⇒ (Q ⇒ R) |
| AXM6 | Q is in H | H ⊢ P ⇒ (¬Q ⇒ R) |
| AXM7 | | H ⊢ P ⇒ P |
| AXM8 | P ∧ ··· contains R | H ⊢ P ∧ ··· ⇒ R |
| AND5 | P ∧ ··· contains A; H ⊢ P ∧ ··· ∧ B ∧ ··· ⇒ R | H ⊢ P ∧ ··· ∧ (A ⇒ B) ∧ ··· ⇒ R |

Note that rule IMP5 has the effect of making the hypotheses
of every sequent that circulates in the proof distinct. This
is true, of course, if such was already the case at the
beginning of the proof (we follow the convention that in
every sequent H ⊢ P submitted to proof, the collection H of
hypotheses is always empty).

### 7.6 New Tactic

Following the addition of the preceding rules, the tactic is
modified as follows, in decreasing priority order:

- any of the rules AXM4, AXM5, AXM6, AXM7, AXM8, AND5,
- any of the rules AND, OR, IMP1, IMP2, IMP3, EQV, NOT,
- any of the rules AXM1, AXM2, AXM3,
- the rule IMP5,
- the rule IMP4.

---

## 8 Predicate Prover

### 8.1 Syntax

This prover can conduct the proof of formulas following the
syntax:

```
prd ::= prd ∧ prd
      | prd ∨ prd
      | prd ⇒ prd
      | prd ⇔ prd
      | ¬ prd
      | ∀ vrb · prd
      | ∃ vrb · prd
      | frm

vrb ::= vrb, idt
      | idt
```

### 8.2 Basic Inference Rules

As in the preceding prover, the new operators ∀ and ∃ induce
different groups of four rules whose consequents have the
following general form (where the symbol ⃝ corresponds to
the quantifiers ∀ or ∃):

| | Antecedents | Consequent |
|---|-------------|------------|
| 1 | ... | H ⊢ ¬(⃝ x · P) ⇒ R |
| 2 | ... | H ⊢ ¬(⃝ x · P) |
| 3 | ... | H ⊢ (⃝ x · P) ⇒ R |
| 4 | ... | H ⊢ ⃝ x · P |

We first find two groups of rules performing the **grouping
of quantifications** of the same kind. First for the
universal quantifier:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| ALL1 | x and y are distinct; H ⊢ ¬(∀(x, y) · P) ⇒ R | H ⊢ ¬(∀x · ∀y · P) ⇒ R |
| ALL2 | x and y are distinct; H ⊢ ¬(∀(x, y) · P) | H ⊢ ¬(∀x · ∀y · P) |
| ALL3 | x and y are distinct; H ⊢ (∀(x, y) · P) ⇒ R | H ⊢ (∀x · ∀y · P) ⇒ R |
| ALL4 | x and y are distinct; H ⊢ ∀(x, y) · P | H ⊢ ∀x · ∀y · P |

Then for the existential quantifier:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| XST1 | x and y are distinct; H ⊢ ¬(∃(x, y) · P) ⇒ R | H ⊢ ¬(∃x · ∃y · P) ⇒ R |
| XST2 | x and y are distinct; H ⊢ ¬(∃(x, y) · P) | H ⊢ ¬(∃x · ∃y · P) |
| XST3 | x and y are distinct; H ⊢ (∃(x, y) · P) ⇒ R | H ⊢ (∃x · ∃y · P) ⇒ R |
| XST4 | x and y are distinct; H ⊢ ∃(x, y) · P | H ⊢ ∃x · ∃y · P |

The use of rules ALL1 to XST4 leads to the formation of
multiple variables of the form x, y. Recall that such
constructions are effectively variables only if x and y are
distinct (hence the side condition). Furthermore, when these
variables x and y are themselves multiple variables, they
must not have common sub-variables, and one must perform a
complementary **flattening**. For example, if x is the
variable a, b and y is the variable c, d, one obtains,
following this flattening, the multiple variable a, b, c, d.

We then find the inference rules proper. First for the
universal quantifier:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| ALL5 | x not free in R; H ⊢ ∀x · (¬P ⇒ R) | H ⊢ ¬(∀x · P) ⇒ R |
| ALL5 | x is free in R; y free in neither P nor R; S = [x := y] P; H ⊢ ∀y · (¬S ⇒ R) | H ⊢ ¬(∀x · P) ⇒ R |
| ALL6 | H ⊢ (∀x · P) ⇒ FALSE | H ⊢ ¬(∀x · P) |
| ALL7 | x not free in H; H, (∀x · P) ⊢ Q | H ⊢ (∀x · P) ⇒ Q |
| ALL7 | x is free in H; y free in neither A nor H; P = [x := y] A; H, (∀x · P) ⊢ Q | H ⊢ (∀x · A) ⇒ Q |
| ALL8 | x not free in H; H ⊢ P | H ⊢ ∀x · P |
| ALL8 | x is free in H; y free in neither P nor H; R = [x := y] P; H ⊢ R | H ⊢ ∀x · P |

As we shall see later in Section 8.12, rule ALL7 will be
modified.

Then for the existential quantifier:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| XST5 | H ⊢ (∀x · ¬P) ⇒ R | H ⊢ ¬(∃x · P) ⇒ R |
| XST51 | H ⊢ (∀x · P) ⇒ R | H ⊢ ¬(∃x · ¬P) ⇒ R |
| XST6 | H ⊢ ∀x · ¬P | H ⊢ ¬(∃x · P) |
| XST61 | H ⊢ ∀x · P | H ⊢ ¬(∃x · ¬P) |
| XST7 | x not free in R; H ⊢ ∀x · (P ⇒ R) | H ⊢ (∃x · P) ⇒ R |
| XST7 | x is free in R; y free in neither P nor R; Q = [x := y] P; H ⊢ ∀y · (Q ⇒ R) | H ⊢ (∃x · P) ⇒ R |
| XST8 | H ⊢ (∀x · ¬P) ⇒ FALSE | H ⊢ ∃x · P |

One sees that rules XST5-XST8 follow from the equivalence
between ¬∃x · P and ∀x
· ¬P. Rule XST8 will be further modified in Section 8.12.

### 8.3 Tactic

The tactic is now as follows, in decreasing priority order:

- any of the rules ALL1, ..., ALL4, XST1, ..., XST4,
- any of the rules ALL5, ..., ALL8, XST5, ..., XST8,
- any of the rules AXM4, AXM5, AXM6, AXM7, AXM8, AND5,
- any of the rules AND, OR, IMP1, IMP2, IMP3, EQV, NOT,
- any of the rules AXM1, AXM2, AXM3,
- the rule IMP5,
- the rule IMP4.

### 8.4 Proof Invariant

It follows from the tactic proposed in the preceding section
that, at a given moment of the proof, the hypotheses H of
the current sequent are constituted only of simple
propositions (introduced by rule IMP4), or of universally
quantified formulas (introduced by rule ALL7).

### 8.5 Syntax Extension

Rule ALL6 and the optimised rule XST8 present a consequent
containing the predicate FALSE in its conclusion. We must
therefore extend the syntax to account for this new
predicate as well as its negation, TRUE.

```
prd ::= prd ∧ prd
      | prd ∨ prd
      | prd ⇒ prd
      | prd ⇔ prd
      | ¬ prd
      | ∀ vrb · prd
      | ∃ vrb · prd
      | TRUE
      | FALSE
      | frm

vrb ::= vrb, idt
      | idt
```

### 8.6 Inference Rules for TRUE and FALSE

Here are the rules for TRUE:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| VR1 | | H ⊢ ¬TRUE ⇒ R |
| VR2 | H ⊢ FALSE | H ⊢ ¬TRUE |
| VR3 | H ⊢ R | H ⊢ TRUE ⇒ R |
| VR4 | | H ⊢ TRUE |

And those for FALSE:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| FX1 | H ⊢ R | H ⊢ ¬FALSE ⇒ R |
| FX2 | | H ⊢ ¬FALSE |
| FX3 | | H ⊢ FALSE ⇒ R |

One notices similarities between VR1 and FX3, VR3 and FX1,
VR4 and FX2. They arise from the equivalence between ¬TRUE
and FALSE. One can observe that the rule FX4 whose
consequent would be H ⊢ FALSE is missing. We will see in the
following sections what treatment is required for a sequent
of this form.

### 8.7 Proof Suspension

Rule ALL6, composed with rule ALL7, generates a sequent of
the form H ⊢ FALSE. More generally, we have the following
rule which is applied **last**, when the proof otherwise
fails:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| STOP | P is not the predicate FALSE; H ⊢ ¬P ⇒ FALSE | H ⊢ P |

Since this rule is applied last, the predicate P is
necessarily a simple proposition. Note that this rule,
composed with rule IMP4 (and possibly with rule NOT1), also
generates a sequent of the form H ⊢ FALSE.

### 8.8 New Tactic

The tactic is now as follows, in decreasing priority order:

- any of the rules ALL1, ..., ALL4, XST1, ..., XST4,
- any of the rules ALL5, ..., ALL8, XST5, ..., XST8,
- any of the rules AXM4, AXM5, AXM6, AXM7, AXM8, AND5,
- any of the rules AND, OR, IMP1, IMP2, IMP3, EQV, NOT, VR,
  FX,
- any of the rules AXM1, AXM2, AXM3,
- the rule IMP5,
- the rule IMP4,
- the rule STOP.

Note that all rules we have introduced, except rules IMP4
and ALL7 which change the hypotheses, are equivalence rules,
in the sense that:

- either they transform a sequent H ⊢ P into no genuine
  sequent (there may of course be side conditions), in which
  case the rule is an axiom,
- or they transform a sequent H ⊢ P into a sequent H ⊢ Q
  where P is equivalent to Q,
- or they transform a sequent H ⊢ P into two sequents H ⊢ Q
  and H ⊢ R where P is equivalent to Q ∧ R.

### 8.9 Principle of Universal Hypothesis Instantiation

When the sequent to be proved is of the form

H ⊢ FALSE

the proof does not necessarily fail; it may enter, where
applicable, a phase of **instantiation of universal
hypotheses**, justified by the following rule:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| INS | H contains ∀x · Q(x); H ⊢ Q(E) ⇒ FALSE | H ⊢ FALSE |

Note that this first version of rule INS is extremely
primitive. We will give its definitive form later (Section
8.22). The application of this rule allows the proof to be
relaunched on the other inference rules. The problem posed
by the application of this rule is, of course, that of
discovering the expression E used to instantiate the
variable x in the predicate Q(x).

We will now explain how we proceed to choose the expression
to use for instantiating such a universal hypothesis. For
this, we assume that our universal hypothesis is in a so-
called **normalised** form:

∀x · ¬(P₁(x) ∧ ··· ∧ Pᵢ(x) ∧ ··· ∧ Pₙ(x))

where n is at least 2, and where each of the predicates
P₁(x), ..., Pᵢ(x), ..., Pₙ(x) can only take one of the
following forms:

- simple proposition,
- normalised universally quantified predicate.

The basic principle for choosing the appropriate
instantiation rests on the existence of another hypothesis
of the form Pᵢ(E). If this is the case, we then instantiate
x with E and the new sequent to prove is (after applying
rule INS):

H ⊢ ¬(P₁(E) ∧ ··· ∧ Pᵢ(E) ∧ ··· ∧ Pₙ(E)) ⇒ FALSE

The proof of this sequent decomposes (rule AND1) into the
proof of each of the following sequents:

- H ⊢ ¬P₁(E) ⇒ FALSE
- ...
- H ⊢ ¬Pᵢ(E) ⇒ FALSE
- ...
- H ⊢ ¬Pₙ(E) ⇒ FALSE

One sees immediately that the sequent H ⊢ ¬Pᵢ(E) ⇒ FALSE is
proved immediately by application of rule AXM2, since we
assumed that the predicate Pᵢ(E) was part of the collection
of hypotheses H. It follows that the sequent to prove upon
application of rule INS can be simplified as follows:

H ⊢ ¬(P₁(E) ∧ ··· ∧ Pₙ(E)) ⇒ FALSE

We have simply removed the predicate Pᵢ(E) which has become
unnecessary. A particularly interesting case is that of a
universal hypothesis of the form:

∀x · ¬(TRUE ∧ P(x))

In the presence of another hypothesis of the form P(E), the
instantiation of x by E then produces the sequent

H ⊢ ¬TRUE ⇒ FALSE

which is immediately proved by application of VR1.

We will later consider (Section 8.19) a generalisation of
this particular case. We will also study the case of partial
instantiations, as well as that of multiple instantiations
(Sections 8.17 and 8.18). We will finally study what should
be done when faced with a collection of hypotheses
containing only quantified predicates or when all
instantiation attempts fail (Section 8.23).

---

### 8.10 Normalisation of Universally Quantified Hypotheses

We have seen that the basic mechanism for instantiating a
universal hypothesis was based on the assumption that it was
**normalised**, i.e. in the form:

∀x · ¬(P₁ ∧ ... ∧ Pᵢ ∧ ... ∧ Pₙ)

where the predicates Pᵢ are either simple propositions, or
normalised universally quantified predicates. Clearly, when
such a universal hypothesis is introduced (by application of
rule ALL7), there is no reason for it to already be
normalised. It is therefore necessary to normalise a
universal hypothesis before applying this rule.

The normalisation of the predicate P in the universal
hypothesis ∀x · P proceeds in three distinct phases,
corresponding to three normal forms: nrm1, nrm2, and nrm3.

The first normal form follows the syntax:

```
nrm1 ::= base1
        | base3 ⇒ nrm1
        | nrm1 ∧ nrm1

base1 ::= smp
         | ∀ vrb · nrm1

base3 ::= smp
         | ∀ vrb · nrm3
```

where `smp` denotes a simple proposition. Note that the
second alternative of base3, i.e. ∀ vrb · nrm3, contains a
predicate already in the third form nrm3 (recursion of the
normalisation). The first normal form nrm1 is obtained
(Section 8.13) using the preceding inference rules, duly
extended through the notion of result.

Example of a predicate in form nrm1:

P ⇒ (Q ⇒ (∀x · ¬(A ∧ ¬B) ⇒ (C ⇒ ∀y · (D ⇒ E))))

The second normal form nrm2 follows the syntax:

```
nrm2 ::= smp
        | conj ⇒ smp

conj ::= base3
        | conj ∧ base3
```

The passage from nrm1 to nrm2 is performed using specific
rules (Section 8.14). Example in nrm2 form:

P ∧ Q ∧ ∀x · ¬(A ∧ ¬B) ∧ C ∧ D ⇒ E

Finally the third normal form nrm3, which is the one we will
exploit in quantified hypotheses:

```
nrm3 ::= ¬(conj ∧ base3)
```

The passage from nrm2 to nrm3 is performed using specific
rules (Section 8.15). Example in nrm3 form:

¬(P ∧ Q ∧ ∀x · ¬(A ∧ ¬B) ∧ C ∧ D ∧ ¬E)

We indeed obtain a predicate in the form of the negation of
a conjunction of predicates that are themselves either
simple predicates or universal quantifications of predicates
in the third normal form.

### 8.11 Inference Rule with Result

To present the mechanisms for transforming a predicate into
its normal form, we need to adjoin to the notion of
inference rule (as briefly presented in Section 6) that of
an inference rule said to be **with result**. More
precisely, such a rule is one whose application produces, as
its name indicates, an ancillary result, which is a certain
predicate. It is represented as follows:

| R | Antecedents | Consequent | Result |
|---|-------------|------------|--------|
| | (Σ₁) ⇝ P₁; ...; (Σₙ) ⇝ Pₙ | Σ | f(P₁, ..., Pₙ) |

where the Σᵢ and Σ denote sequents, where the Pᵢ denote the
**results of the proofs** of the sequents Σᵢ, and where the
formula f(P₁, ..., Pₙ) denotes the **result** of rule R. The
notation Σ ⇝ P reads: the proof of sequent Σ gives result P.

The result of the proof of a sequent is, by definition, the
result of the rule applied to this sequent to prove it
successfully.

### 8.12 Normalisation Mechanism

The normalisation must clearly be initiated upon application
of rule ALL7, since this rule is the only one that can
introduce universally quantified hypotheses. This rule must
now be modified so that the proof of the consequent

H ⊢ (∀x · P) ⇒ Q

no longer has the effect of promoting the predicate ∀x · P
to a hypothesis, but rather a predicate equivalent to it and
suitably normalised. In other words, the proof of this
sequent must now reduce to that of a sequent of the form

H, (∀x · T) ⊢ Q

where T is a predicate in the third normal form nrm3 and
equivalent to P. The new rule ALL7:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| ALL7 | x not free in H; (H ⊢ P) ⇝ R; H ⊢ (♢x · R) ⇒ Q | H ⊢ (∀x · P) ⇒ Q |
| ALL7 | x is free in H; y free in neither A nor H; P = [x := y] A; (H ⊢ P) ⇝ R; H ⊢ (♢x · R) ⇒ Q | H ⊢ (∀x · A) ⇒ Q |

In this rule, the proof of the first antecedent H ⊢ P is
assumed to give a result R, in first normal form and
equivalent to P. The second antecedent H ⊢ (♢x · R) ⇒ Q
contains the quantifier ♢ whose role is to repaint the
universal quantifier ∀ so as not to relaunch rule ALL7. The
proof of this second antecedent will reduce (as a first
approximation, as we shall see in Section 8.14) to that of a
sequent of the form

H ⊢ (♢x · S) ⇒ Q

where S is in second normal form nrm2. Finally (Section
8.15), the proof of this last sequent will reduce to that of

H ⊢ (♡x · T) ⇒ Q

where T is in third normal form nrm3. It then only remains
to apply rule ALL9:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| ALL9 | H, (∀x · T) ⊢ Q | H ⊢ (♡x · T) ⇒ Q |

Rule XST8 is also modified by composition with ALL7:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| XST8 | x not free in H; (H ⊢ ¬P) ⇝ R; H ⊢ (∀x · R) ⇒ FALSE | H ⊢ ∃x · P |
| XST8 | x is free in H; y free in neither A nor H; P = [x := y] A; (H ⊢ ¬P) ⇝ R; H ⊢ (∀x · R) ⇒ FALSE | H ⊢ (∃x · A) |

### 8.13 First Normalisation

In the new rule ALL7, the first antecedent H ⊢ P is proved
from the same rules as before (slightly transformed
however), namely AND, OR, IMP, EQV, AXM, ALL, XST, VR, FX,
STOP, plus the NRM rules and rule ALL9. However, all these
rules are transformed so as to produce a result. The
transformations follow these schemas (primed names
distinguish transformed from original rules):

- **Schema 0** (rules without genuine antecedents, except
  STOP): Result is TRUE
- **Schema 1** (rules with one antecedent, except IMP4,
  ALL8, ALL9): If (H ⊢ P) ⇝ R, then result is R
- **Schema 2** (rules with two antecedents, except ALL7): If
  (H ⊢ P) ⇝ S and (H
  ⊢ Q) ⇝ T, then result is S ∧ T

Special cases:

| Rule | Antecedents | Consequent | Result |
|------|-------------|------------|--------|
| IMP4′ | (H, P ⊢ Q) ⇝ R | H ⊢ P ⇒ Q | P ⇒ R |
| ALL7′ | x not free in H; (H ⊢ P) ⇝ R; (H ⊢ (♢x · R) ⇒ Q) ⇝ S | H ⊢ (∀x · P) ⇒ Q | S |
| ALL8′ | x not free in H; (H ⊢ P) ⇝ Q | H ⊢ ∀x · P | ∀x · Q |
| ALL8′ | x is free in H; y free in neither P nor H; R = [x := y] P; (H ⊢ R) ⇝ Q | H ⊢ ∀x · P | ∀y · Q |
| ALL9′ | (H, (∀x · P) ⊢ Q) ⇝ R | H ⊢ (♡x · P) ⇒ Q | (∀x · P) ⇒ R |
| STOP′ | | H ⊢ P | P |

### 8.14 Passage from First to Second Normalisation

The passage from first to second normalisation is performed
by rules that all apply to consequents of the form:

H ⊢ (♢x · P) ⇒ S

where P is in first normal form nrm1. The first four rules
eliminate predicates that do not depend on the quantified
variable x:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| NRM1 | x not free in P; H ⊢ P ⇒ S | H ⊢ (♢x · P) ⇒ S |
| NRM2 | x not free in P; H ⊢ (P ⇒ ♢x · Q) ⇒ S | H ⊢ ♢x · (P ⇒ Q) ⇒ S |
| NRM3 | x not free in Q; Q is not FALSE; H ⊢ (Q ⇒ S) ∧ ((∀x · ¬P) ⇒ S) | H ⊢ ♢x · (P ⇒ Q) ⇒ S |
| NRM4 | x not free in Q; H ⊢ (Q ⇒ ♢x · (P ⇒ R)) ⇒ S | H ⊢ ♢x · (P ⇒ (Q ⇒ R)) ⇒ S |
| NRM5 | H ⊢ ♢x · (P ∧ Q ⇒ R) ⇒ S | H ⊢ ♢x · (P ⇒ (Q ⇒ R)) ⇒ S |

The following rules decompose conjunctions:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| NRM6 | H ⊢ ♢x · (R ⇒ P) ⇒ (♢x · (R ⇒ Q) ⇒ S) | H ⊢ ♢x · (R ⇒ P ∧ Q) ⇒ S |
| NRM7 | H ⊢ (♢x · P) ⇒ ((♢x · Q) ⇒ S) | H ⊢ ♢x · (P ∧ Q) ⇒ S |

The last rules suppress eventual quantifications:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| NRM8 | x and y are distinct; H ⊢ (♢(x, y) · Q) ⇒ S | H ⊢ (♢x · ∀y · Q) ⇒ S |
| NRM8 | x and y not distinct; z distinct from x and y; K = [y := z] Q; H ⊢ (♢(x, y) · K) ⇒ S | H ⊢ (♢x · ∀y · Q) ⇒ S |
| NRM9 | x and y are distinct; y not free in P; H ⊢ ♢(x, y) · (P ⇒ Q) ⇒ S | H ⊢ ♢x · (P ⇒ ∀y · Q) ⇒ S |
| NRM9 | x and y not distinct, or y free in P; z distinct from x, not free in P or Q; K = [y := z] Q; H ⊢ ♢(x, z) · (P ⇒ K) ⇒ S | H ⊢ ♢x · (P ⇒ ∀y · Q) ⇒ S |

### 8.15 Passage from Second to Third Normalisation

The passage from second to third normalisation is performed
by rules applying to consequents of the form H ⊢ (♢x · P) ⇒
S where P is in second normal form nrm2:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| NRM10 | H ⊢ ♡x · ¬(P ∧ Q) ⇒ R | H ⊢ ♢x · (P ∧ Q ⇒ FALSE) ⇒ R |
| NRM11 | H ⊢ ♡x · ¬(TRUE ∧ P) ⇒ R | H ⊢ ♢x · (P ⇒ FALSE) ⇒ R |
| NRM12 | H ⊢ ♡x · ¬(P ∧ Q) ⇒ R | H ⊢ ♢x · (P ⇒ ¬Q) ⇒ R |
| NRM13 | H ⊢ ♡x · ¬(P ∧ ¬Q) ⇒ R | H ⊢ ♢x · (P ⇒ Q) ⇒ R |
| NRM14 | H ⊢ ♡x · ¬(TRUE ∧ P) ⇒ R | H ⊢ (♢x · ¬P) ⇒ R |
| NRM15 | H ⊢ ♡x · ¬(TRUE ∧ ¬P) ⇒ R | H ⊢ (♢x · P) ⇒ R |

Before promoting the quantified predicate to a hypothesis
via ALL9, we check whether this is necessary:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| NRM16 | ∀x · P is in H | H ⊢ (♡x · P) ⇒ Q |

### 8.16 Discovery of Contradictions on Hypothesis Promotion

As an additional optimisation, the following four rules
allow simple contradictions to be found upon promotion of a
predicate to a hypothesis:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| AXM9 | ∀x · ¬(TRUE ∧ P) is in H; there exists E such that [x := E] P = R | H ⊢ R ⇒ Q |
| NRM17 | ∀x · ¬(TRUE ∧ P) is in H; there exists E such that [x := E] P = R | H ⊢ ♡y · ¬(TRUE ∧ ¬R) ⇒ Q |
| NRM18 | ∀x · ¬(TRUE ∧ ¬P) is in H; there exists E such that [x := E] P = R | H ⊢ ♡y · ¬(TRUE ∧ R) ⇒ Q |
| NRM19 | P is in H; there exists E such that [x := E] R = P | H ⊢ ♡x · ¬(TRUE ∧ R) ⇒ Q |

---

### 8.17 Partial Instantiation of a Universal Hypothesis

We now return to the mechanism for instantiating a universal
hypothesis. This problem arises when the collection of
hypotheses H contains, for example, a universal hypothesis
of the form:

∀(x, y, z) · ¬(P₁(x, y, z) ∧ P₂(y) ∧ P₃(x, y, z))

and another hypothesis of the form P₂(e). In this case, we
can **partially instantiate** the universal hypothesis by
removing y from the quantification and instantiating it by
e:

∀(x, z) · ¬(P₁(x, e, z) ∧ P₃(x, e, z))

This partial instantiation can apply to several variables
simultaneously. For example, with the hypothesis ∀(x, y, z)
· ¬(P₁(y, z) ∧ P₂(x, y, z)) and the simple hypothesis P₁(e,
f), we obtain:

∀x · ¬P₂(x, e, f)

### 8.18 Unification of Complementary Partial Instantiations

When the predicate prover enters the phase of instantiating
universal hypotheses, we always try to have it perform as
many instantiations (partial or total) as possible. When two
(or more) of these instantiations bear on the **same
universal hypothesis** but on **different variables**, we
can generate the additional instantiation resulting from the
combination of these instantiations.

For example, suppose we have the universal hypothesis:

∀(x, y, z) · ¬(P₁(x) ∧ P₂(y) ∧ P₃(z) ∧ P₄(x, y, z))

together with the three simple hypotheses P₁(e), P₂(f), and
P₃(g). Taken separately, these can generate partial
instantiations. But we can accelerate the mechanism by
directly instantiating the triple x, y, z with e, f, g to
obtain the total instantiation ¬P₄(e, f, g).

To systematise this mechanism, during the analysis of a
universal hypothesis, we construct a table T0 of partial
instantiations of the quantified variables. Upon discovery
of a new partial instantiation for the same hypothesis, we
try to unify it with those already in T0.

### 8.19 Searching for Contradiction during the Instantiation Phase

We consider the mechanism by which a multiple instantiation
can lead directly to a contradiction. Suppose we have the
universal hypothesis:

∀(x, y) · ¬(P₁(x) ∧ P₂(y))

and the two simple hypotheses P₁(f) and P₂(g). The
instantiation resulting from replacing the pair x, y by f, g
is the empty instantiation. The explanation is that we can
replace the preceding hypothesis by the equivalent:

∀(x, y) · ¬(TRUE ∧ P₁(x) ∧ P₂(y))

This hypothesis then leads, after instantiation, to the
sequent H ⊢ ¬TRUE ⇒ FALSE, which is proved instantly by rule
VR1.

### 8.20 Analysis of the Different Forms of Instantiations

The instantiations that can be obtained necessarily belong
to one of four categories:

1. **A simple proposition.** For example, with ∀(x, y) ·
   ¬(P(x) ∧ ¬Q(y) ∧ R(x, y)) and hypotheses P(e) and ¬Q(f),
   we obtain the instantiation ¬R(e, f). These are very
   interesting as they allow discovery of new instantiations
   in a later phase.

2. **The negation of a universal quantification.** For
   example, obtaining ¬∀z · ¬(A(e, z) ∧ B(f, z)), which can
   be replaced by an existential quantification ∃z · (A(e,
   z) ∧ B(f, z)), promoting simple hypotheses A(e, z) and
   B(f, z) which can themselves lead to new instantiations.

3. **A universal quantification.** A partial instantiation.
   It is not interesting to promote these as hypotheses
   since they do not provide additional information.

4. **The negation of a conjunction of simple propositions or
   universally quantified predicates.** These are the only
   ones that pose a problem as they trigger **proofs by
   cases** which can be very costly. The following section
   shows how to simplify them.

### 8.21 Simplification of Instantiations

An instantiation of the form ¬(P ∧ Q ∧ R) can be simplified
using simple instantiations obtained elsewhere. This
instantiation gives rise to proving:

- H, ¬P ⊢ FALSE
- H, ¬Q ⊢ FALSE
- H, ¬R ⊢ FALSE

If we also have the simple instantiation Q, then the second
sequent is discharged immediately. The same effect is
obtained more directly by eliminating Q from the
instantiation ¬(P ∧ Q ∧ R) to obtain ¬(P ∧ R). If P is also
a simple instantiation, we obtain another simple
instantiation ¬R. If R itself is a simple instantiation, we
have a contradiction found during the instantiation phase.

To systematise this, we construct the following tables:

- **Table T1**: all total instantiations.
- **Table T2**: simple propositions — for each simple
  proposition A, B, C, ... appearing in instantiations of
  the form ¬(A ∧ B ∧ C ∧ ···), the list of corresponding
  indices in T1.
- **Table T3**: simple instantiations.

The section then gives a detailed worked example showing how
iterative simplification using tables T1, T2, and T3 can
discover contradictory instantiations ¬Q(e) and Q(e).

### 8.22 Final Algorithm for Universal Hypothesis Instantiation

The previous sections have shown the different mechanisms at
work in the instantiation of universal hypotheses. This
section synthesises them into a single algorithm, proceeding
by a series of nested loops:

```
(0) For each universal hypothesis of the form ∀x · ¬P
    Clean table T0 of partial instantiations
    (1) For each simple hypothesis R and each simple proposition S of P
        If there exists an instantiation I of variables x making S equal to R
        (2) If I is total
            (3) Perform the substitution corresponding to I
                Obtain a formula F of the form ¬(A ∧ B ∧ ···)
                Simplify F (eliminate simple instantiations from T3)
                (NB: this simplification may lead to contradiction)
            (4) Store F in table T1
                If F is of the form ¬∀z · ¬Q: stop processing here
                If F is of the form ¬(A ∧ B ∧ ···): update T2
                If F is a simple proposition:
                (5) Store F in T3
                    For each index i in the list of F in T2
                    (6) Simplify instantiation at index i in T1
                    (7) Obtain formula H
                    (8) Update entry i of T1 with H
                        If H is itself a simple proposition:
                        repeat steps (5)-(8) on H
        (9) If I is partial
            (10) For each partial instantiation J in T0
                 (11) If I and J can be unified into K
                      (12) If K is partial: store in T0
                      (13) If K is total: repeat steps (3)-(8) on K
            (14) Store I in T0
```

At the end of this process, we obtain either the unique
instantiation FALSE (if contradiction was found), forming
the sequent H ⊢ FALSE ⇒ FALSE, or the (possibly empty) list
Q₁, Q₂, ..., Qₙ of retained instantiations, forming:

H ⊢ Q₁ ⇒ (Q₂ ⇒ ... (Qₙ ⇒ FALSE) ...)

The instantiations are sorted so that simple instantiations
and those of the form ¬∀x · ¬P come first, followed by those
of the form ¬(A ∧ B ∧ ...) which generate proofs by cases.

In summary, the rule INS can now be written:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| INS | Determination of instantiations Q₁, ..., Qₙ; H ⊢ Q₁ ⇒ (Q₂ ⇒ ... (Qₙ ⇒ FALSE) ...) | H ⊢ FALSE |

### 8.23 Particular Instantiations

**Case of universal hypotheses containing no simple
propositions.** Such hypotheses can never be instantiated
with the approach just described. We then apply the
simplistic technique of instantiating such hypotheses with
so-called **known variables**. By definition, the variable x
becomes known upon the suppression of the universal
quantification ∀x on the sequent H ⊢ ∀x · P by application
of rule ALL8.

**What to do when no instantiation could take place.** When
this case occurs on a hypothesis of the form ∀x · P, we
simply instantiate x by x.

We are well aware that the techniques just proposed are only
stopgaps. In the context of a future study, this issue
should be developed further.

### 8.24 New Tactic

The tactic is now as follows, in decreasing priority order:

- any of the rules ALL1, ..., ALL4, XST1, ..., XST4,
- any of the rules ALL5, ..., ALL8, XST5, ..., XST8,
- any of the rules AXM4, AXM5, AXM6, AXM7, AXM8, AND5,
- any of the rules AND, OR, IMP1, IMP2, IMP3, EQV, NOT, VR,
  FX,
- any of the rules AXM1, AXM2, AXM3,
- the rule IMP5,
- the rule AXM9,
- the NRM rules in their natural order,
- the rule ALL9,
- the rule IMP4,
- the rule INS,
- the rule STOP.

---

## 9 Predicate Prover with Equality

We now extend the predicate prover by introducing equality.
This last prover accepts predicates following the syntax
presented in Chapter 4.

Equality is characterised by a number of properties,
including:

| Property | Formulation |
|----------|-------------|
| Reflexivity | E = E |
| Commutativity | (E = F) ⇔ (F = E) |
| Leibniz's Law | (E = F) ⇒ ([x := E]P ⇔ [x := F]P) |
| One-Point Rule | ∀x · (x = E ⇒ P) ⇔ [x := E]P (if x is not free in E) |

These properties induce a number of inference rules, which
we present in the remainder of this section.

### 9.1 Special Rules due to Reflexivity of Equality

The following rules constitute an extension of the VR rules
concerning the predicate TRUE (Section 8.6). They are a
consequence of the equivalence between TRUE and E = E.

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| EVR1 | | H ⊢ ¬(E = E) ⇒ P |
| EVR2 | H ⊢ FALSE | H ⊢ ¬(E = E) |
| EVR3 | H ⊢ P | H ⊢ (E = E) ⇒ P |
| EVR4 | | H ⊢ (E = E) |

The following rule is an optimisation of EVR1 on numerical
values:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| EVR11 | n ∈ ℕ; m ∈ ℕ; n ≠ m | H ⊢ (n = m) ⇒ P |

### 9.2 Special Rules due to Commutativity of Equality

The rules in this section are due to the equivalence between
E = F and F = E. They constitute special cases of rules
containing multiple occurrences of the same predicate.

Each of the rules AXM1, AXM2, AXM3 assumes the presence of
the **same occurrence** of predicate P in its consequent and
antecedent. They therefore induce the following special
rules when P takes the form E = F (or ¬(E = F)):

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| EAXM1 | ¬(F = E) is in H | H ⊢ (E = F) ⇒ P |
| EAXM2 | (F = E) is in H | H ⊢ ¬(E = F) ⇒ P |
| EAXM31 | (F = E) is in H | H ⊢ (E = F) |
| EAXM32 | ¬(F = E) is in H | H ⊢ ¬(E = F) |

Likewise, rule IMP5 induces the following rules. Thanks to
these rules, one cannot simultaneously have the hypotheses E
= F and F = E, nor ¬(E = F) and ¬(F = E):

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| EIMP51 | ¬(F = E) is in H; H ⊢ P | H ⊢ ¬(E = F) ⇒ P |
| EIMP52 | (F = E) is in H; H ⊢ P | H ⊢ (E = F) ⇒ P |

Rule AXM9 induces two extensions:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| EAXM91 | ∀x · ¬(TRUE ∧ p = q) is in H; there exists E such that [x := E](q = p) reduces to (a = b) | H ⊢ (a = b) ⇒ Q |
| EAXM92 | ∀x · ¬(TRUE ∧ ¬(p = q)) is in H; there exists E such that [x := E](q = p) reduces to (a = b) | H ⊢ ¬(a = b) ⇒ Q |

### 9.3 One-Point Rules

The one-point rule allows simplifying a predicate of the
form ∀x · (x = E ⇒ P) into the equivalent predicate [x :=
E]P (if x has no free occurrences in E). A slightly
different but nevertheless equivalent case corresponds to
the sequent

H ⊢ x = E ⇒ P

where x is assumed to have no free occurrences in H and in
E. In this case, the proof of this sequent is the same as
that of H ⊢ ∀x · (x = E ⇒ P). It suffices to apply rule ALL8
in reverse.

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| OPR1 | x is a variable; x not free in H; x not free in E; Q = [x := E] P; H ⊢ Q | H ⊢ (x = E) ⇒ P |
| OPR2 | x is a variable; x not free in H; x not free in E; Q = [x := E] P; H ⊢ Q | H ⊢ (E = x) ⇒ P |

We now apply the one-point rule proper to normalised
universal quantifications, before their promotion to a
hypothesis. They are in the general form:

♡(x₁, ..., xᵢ, ..., xₙ) · ¬(P₁ ∧ ··· ∧ Pⱼ ∧ ··· ∧ Pₘ)

Suppose predicate Pⱼ takes the form xᵢ = E (where E does not
depend on xᵢ). The preceding predicate is then equivalent
to:

♡(x₁, ..., xₙ) · ¬([xᵢ := E]P₁ ∧ ··· ∧ [xᵢ := E]Pₘ)

Note that when n equals 1, the quantification disappears
completely.

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| NRM20 | x not free in E; H ⊢ ♡y · ¬[x := E]P ⇒ Q | H ⊢ ♡(x, y) · ¬(P ∧ x = E) ⇒ Q |
| NRM21 | x not free in E; H ⊢ ♡y · ¬[x := E]P ⇒ Q | H ⊢ ♡(x, y) · ¬(P ∧ E = x) ⇒ Q |
| NRM22 | x not free in E; H ⊢ ¬[x := E]P ⇒ Q | H ⊢ ♡x · ¬(P ∧ x = E) ⇒ Q |
| NRM23 | x not free in E; H ⊢ ¬[x := E]P ⇒ Q | H ⊢ ♡x · ¬(P ∧ E = x) ⇒ Q |

Recall that the normal form of a universally quantified
hypothesis must contain at least **two** predicates (see
Section 8.9). By the reductions just considered, this number
may be reduced to one. We restore this property with:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| NRM24 | P is not of the form A ∧ B; H ⊢ ♡x · ¬(TRUE ∧ P) ⇒ Q | H ⊢ ♡x · ¬P ⇒ Q |

### 9.4 Contradictions due to Equalities

The presence (or promotion) of an equality as a hypothesis
can generate contradictions.

First, two rules for contradiction due to the promotion of
an equality hypothesis:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| ECTR1 | ¬Q is in H; replacing E by F in Q gives R; R is in H | H ⊢ (E = F) ⇒ P |
| ECTR2 | ¬Q is in H; replacing E by F in Q gives R; R is in H | H ⊢ (F = E) ⇒ P |

Then four rules for contradiction due to the presence of an
equality hypothesis:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| ECTR3 | E = F is in H; replacing E by F in P gives R; R is in H | H ⊢ ¬P ⇒ Q |
| ECTR4 | F = E is in H; replacing E by F in P gives R; R is in H | H ⊢ ¬P ⇒ Q |
| ECTR5 | E = F is in H; replacing E by F in P gives R; ¬R is in H | H ⊢ P ⇒ Q |
| ECTR6 | F = E is in H; replacing E by F in P gives R; ¬R is in H | H ⊢ P ⇒ Q |

### 9.5 New Tactic

The tactic is now as follows, in decreasing priority order:

- any of the rules ALL1, ..., ALL4, XST1, ..., XST4,
- any of the rules ALL5, ..., ALL8, XST5, ..., XST8,
- any of the rules AXM4, AXM5, AXM6, AXM7, AXM8, AND5,
- any of the rules AND, OR, IMP1, IMP2, IMP3, EQV, NOT, VR,
  EVR, FX,
- any of the rules AXM1, AXM2, AXM3, EAXM,
- the rules IMP5, EIMP5,
- the rule AXM9,
- the NRM rules in their natural order,
- the OPR rules,
- the ECTR rules,
- the rule ALL9,
- the rule IMP4,
- the rule INS,
- the rule STOP.

## 10 Extension of the Predicate Prover

In this chapter, we present an extension of the Predicate
Prover (PP) consisting essentially of integrating a
**substantial treatment of arithmetic inequalities**.
Similar work (described in another document) was carried out
for the Set Translator so that it remains coherent with the
Predicate Prover.

This extension is realised using two programs that already
exist: the **Arithmetic Prover** and the **Arithmetic
Solver**. These two programs have been incorporated without
changes into the predicate prover. We show here how the
integration of these two programs is realised (launches,
parameters), but also how the implementation of short-
circuits avoids calling them in certain simple cases that
can be handled directly.

We also took the opportunity to make some ancillary
improvements concerning, among other things, the treatment
of equality hypotheses.

### 10.1 Nature of Arithmetic Predicates

Before beginning the description proper, it is important to
note that the arithmetic predicates handled by PP are all
previously normalised by the Set Translator. They therefore
systematically take the form:

E ≤ 0

where E is an integer arithmetic expression constructed from
the operators: +,
−, ×, /, mod.

Note that − is both unary and binary. In principle, the two
binary operators / and mod (integer division and modulo) do
not appear in PP as they are previously axiomatised by the
Set Translator. During the course of the proof, the negation
of a normalised arithmetic predicate may appear: ¬(E ≤ 0).
There exists a rule to normalise such a predicate.

### 10.2 Launching Arithmetic or Equality Processing

The processing of arithmetic or equality hypotheses is
launched on two quite distinct occasions: either when the
goal to prove is FALSE, or when it is of the form ¬(P ∧ Q ∧
···) ⇒ FALSE (note that the antecedent of this implication
must correspond to an instantiation of a universal
hypothesis). In both cases, it is a matter of searching for
a potential contradiction by means of new hypotheses.

#### 10.2.1 First Case

The processing of arithmetic hypotheses consists first of
selecting them, then launching the arithmetic prover, which
determines if they are globally contradictory. To avoid
repeating an unsuccessful processing already performed, we
memoise the hypotheses submitted to the arithmetic prover at
each launch.

The processing of equality hypotheses consists of selecting
one by one the hypotheses of the form x = E or E = x, where
x is a variable not free in E. We then transform each of
them into a substitution x := E, which then acts on all
other hypotheses containing free occurrences of x. This
procedure has the consequence of generating new hypotheses
that may contradict others.

It is in this case also that the search for instantiations
of universal hypotheses is launched.

#### 10.2.2 Second Case

We launch the same processing as above in the hope of
discovering the contradiction before triggering a proof by
cases. Indeed, a goal of the form ¬(P ∧ Q ∧ ···) ⇒ FALSE
will successively lead to proofs of ¬P ⇒ FALSE, ¬Q ⇒ FALSE,
etc. It is preferable, if the contradiction is already
present, to discover it immediately.

Note that in this case, instantiation search is also
launched, but discovered instantiations are not promoted; we
simply check directly whether they are contradictory among
themselves or with others. Indeed, in case of failure,
generating new instantiations would risk indefinitely
biasing the process (the proof by cases might never be
performed).

#### 10.2.3 Conclusion

As can be seen, the three mechanisms — search for
instantiations of universal hypotheses, treatment of
arithmetic hypotheses, and treatment of equality hypotheses
— have exactly the same goal: finding the contradiction in
the hypotheses. It is therefore natural that the launches of
these three treatments are performed under completely
similar conditions.

### 10.3 Impact of Arithmetic Hypothesis Processing on PP

#### 10.3.1 Some Common-Sense Rules

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| AR1 | H ⊢ R | H ⊢ E ≤ E ⇒ R |
| AR2 | a is numeric; b is numeric; a > b | H ⊢ a ≤ b ⇒ R |
| AR3 | H ⊢ 1 − a ≤ 0 ⇒ R | H ⊢ ¬(a ≤ 0) ⇒ R |

#### 10.3.2 Direct Discovery of an Arithmetic Contradiction

A short-circuit to avoid calling the Arithmetic Prover in a
simple and relatively frequent case:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| AR4 | F ≤ 0 is in H; E + F > 0 | H ⊢ E ≤ 0 ⇒ R |

#### 10.3.3 Discovery of Equalities by Analysis of Arithmetic Predicates

Two inequalities can hide an equality that may prove useful
for discovering contradictions:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| AR5 | a ≤ 0 is in H; H ⊢ −a ≪ 0 ⇒ (a = 0 ⇒ R) | H ⊢ −a ≤ 0 ⇒ R |
| AR6 | −a ≤ 0 is in H; H ⊢ a ≪ 0 ⇒ (a = 0 ⇒ R) | H ⊢ a ≤ 0 ⇒ R |
| AR7 | c + b ≤ 0 is in H; a + c = 0; H ⊢ b = a ⇒ (a − b ≪ 0 ⇒ R) | H ⊢ a − b ≤ 0 ⇒ R |
| AR8 | a − b ≤ 0 is in H; a + c = 0; H ⊢ b = a ⇒ (c + b ≪ 0 ⇒ R) | H ⊢ c + b ≤ 0 ⇒ R |

The use of the symbol ≪ avoids looping by applying the
inequality rules always on the same expression.

In the theory ppReduction1X, the goals are not all of the
form P ⇒ Q. These four rules are therefore supplemented:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| AR5_2 | a ≤ 0 is in H; H ⊢ a = 0 ⇒ ¬(−a ≪ 0) | H ⊢ ¬(−a ≤ 0) |
| AR6_2 | −a ≤ 0 is in H; H ⊢ a = 0 ⇒ ¬(a ≪ 0) | H ⊢ ¬(a ≤ 0) |
| AR7_2 | c + b ≤ 0 is in H; a + c = 0; H ⊢ b = a ⇒ ¬(a − b ≪ 0) | H ⊢ ¬(a − b ≤ 0) |
| AR8_2 | a − b ≤ 0 is in H; a + c = 0; H ⊢ b = a ⇒ ¬(c + b ≪ 0) | H ⊢ ¬(c + b ≤ 0) |

The following rules promote expressions of the form a ≪ b to
a hypothesis and eliminate this operator:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| AR12 | H, (a ≤ b) ⊢ P | H ⊢ (a ≪ b) ⇒ P |
| AR13 | 1 − a = b; H ⊢ (b ≤ 0) | H ⊢ ¬(a ≪ 0) |

#### 10.3.4 Calling the Arithmetic Solver

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| AR9 | solver(E) = F; H ⊢ F ≤ 0 ⇒ R | H ⊢ E ≤ 0 ⇒ R |
| AR10 | solver(P) = Q; H ⊢ Q ⇒ R | H ⊢ P ⇒ R |
| AR11 | | H ⊢ not(x ≤ x) ⇒ P |

#### 10.3.5 Influence of Arithmetic on Instantiation Search

Some common-sense rewriting rules applied in the simplifier
of the instantiation system:

| Condition and Left-Hand Side | Right-Hand Side |
|------------------------------|-----------------|
| 0 ≤ 0 | TRUE |
| n is a positive natural number; n ≤ 0 | FALSE |
| n is a natural number; −n ≤ 0 | TRUE |

#### 10.3.6 Arithmetic Pattern-Matching

In the case of arithmetic hypotheses, the search for
instantiations tries to match a simple hypothesis A ≤ 0 with
a quantified hypothesis ∀x · ¬(··· ∧ B(x) ≤ 0 ∧ ···). It
seeks an instantiation E for x such that A = B(E). For this,
we try to put B(x) in one of the two forms C + x or C − x,
where C does not depend on x. The instantiation is then A −
C in the first case and C − A in the second.

Note that this mechanism currently only applies to universal
hypotheses containing a single quantified variable x.
Experience has shown that this mechanism can sometimes
generate very many useless instantiations. Furthermore,
experience has also shown that its use is not required in
the vast majority of cases we have tried. Consequently, this
mechanism is currently only used on a particular call of PP.

#### 10.3.7 Use of the Arithmetic Solver in Normalisation Rules

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| NRM27 | (xᵢ ≤ 0) is in (P ∧ ... ∧ Q); (−xᵢ ≤ 0) is in (P ∧ ... ∧ Q); R = [xᵢ := 0](P ∧ ... ∧ Q); H ⊢ ♢(x₁,...,xᵢ₋₁,xᵢ₊₁,...,xₙ) · ¬R | H ⊢ ♡(x₁,...,xₙ) · ¬(P ∧ ... ∧ Q) |
| NRM28 | (x ≤ 0) is in (P ∧ ... ∧ Q); (−x ≤ 0) is in (P ∧ ... ∧ Q); S = [x := 0](P ∧ ... ∧ Q); H ⊢ ¬(S) ⇒ R | H ⊢ (♡(x) · ¬(P ∧ ... ∧ Q)) ⇒ R |
| NRM29 | (a + xᵢ ≤ 0) is in (P ∧ ... ∧ Q); (b − xᵢ ≤ 0) is in (P ∧ ... ∧ Q); solver(a + b) = 0; S = [xᵢ := b](P ∧ ... ∧ Q); H ⊢ ♢(x₁,...,xᵢ₋₁,xᵢ₊₁,...,xₙ) · ¬S ⇒ R | H ⊢ (♡(x₁,...,xₙ) · ¬(P ∧ ... ∧ Q)) ⇒ R |
| NRM29_1 | (xᵢ + a ≤ 0) is in (P ∧ ... ∧ Q); (−xᵢ + b ≤ 0) is in (P ∧ ... ∧ Q); solver(a + b) = 0; S = [xᵢ := b](P ∧ ... ∧ Q); H ⊢ ♢(x₁,...,xᵢ₋₁,xᵢ₊₁,...,xₙ) · ¬S ⇒ R | H ⊢ (♡(x₁,...,xₙ) · ¬(P ∧ ... ∧ Q)) ⇒ R |
| NRM30 | (a + x ≤ 0) is in (P ∧ ... ∧ Q); (b − x ≤ 0) is in (P ∧ ... ∧ Q); solver(a + b) = 0; S = [x := b](P ∧ ... ∧ Q); H ⊢ ¬S ⇒ R | H ⊢ (♡x · ¬(P ∧ ... ∧ Q)) ⇒ R |
| NRM30_1 | (x + a ≤ 0) is in (P ∧ ... ∧ Q); (−x + b ≤ 0) is in (P ∧ ... ∧ Q); solver(a + b) = 0; S = [x := b](P ∧ ... ∧ Q); H ⊢ ¬S ⇒ R | H ⊢ (♡x · ¬(P ∧ ... ∧ Q)) ⇒ R |

### 10.4 Miscellaneous Improvements

#### 10.4.1 Treatment of Equality Hypotheses

The presence of two equality hypotheses of the form E = F
and E = G (or G = E), where E, F and G are arbitrary
expressions (none of them necessarily designates a
variable), must lead to the generation of the additional
hypothesis F = G.

#### 10.4.2 Verbose Mode of PP

In the verbose mode of PP, the mention "ACTION OF EQUALITY x
= E" has been added to signal the action of a certain
equality, for example x = E, on other hypotheses. The newly
generated hypotheses are then mentioned.

In this way, the three mechanisms for generating additional
hypotheses (instantiations, arithmetic, and equality) are
now at the same level.

#### 10.4.3 Treatment of Set Equalities

Equalities between sets, i.e. E = F, are cancelled (as
equalities) by the Set Translator, which replaces them by
the predicate ∀x · (x ∈ E ⇔ x ∈ F). In other words, PP no
longer directly sees the equality between E and F. This can
cause certain proofs to fail in which one encounters, for
example, expressions of the form f(E), which therefore
cannot be rewritten f(F).

To work around these problems, when such an equality E = F
is encountered by the Set Translator, and in the case where
E and F are both simple variables, it generates the
predicate eql_set(E, F). PP handles such predicates with the
two following rules:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| EQS1 | H ⊢ E = F ⇒ R | H ⊢ eql_set(E, F) ⇒ R |
| EQS2 | H ⊢ FALSE ⇒ R | H ⊢ ¬eql_set(E, F) ⇒ R |

The first rule serves to explicitly promote the set equality
to a hypothesis. The second serves to ignore the proof of
such a predicate.

#### 10.4.4 Suppression of Useless Quantified Variables

Two rules that were missing in the normalisation of
universal hypotheses. They serve to suppress a useless
quantified variable:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| NRM25 | x not free in P; H ⊢ P | H ⊢ ♡(x) · P |
| NRM26 | y not free in P; H ⊢ ♡(x, ...) · P | H ⊢ ♡(x, y, ...) · P |

#### 10.4.5 Equality between Pairs

Two rules that were clearly missing for reducing certain
equalities between ordered pairs, equalities that can appear
during the proof. Such equalities appearing in the original
lemma have already been reduced by the Set Translator:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| EQC1 | H ⊢ ¬(a = c) ∨ ¬(b = d) ⇒ P | H ⊢ ¬((a, b) = (c, d)) ⇒ P |
| EQC2 | H ⊢ (a = c) ∧ (b = d) ⇒ P | H ⊢ ((a, b) = (c, d)) ⇒ P |

#### 10.4.6 Treatment of Booleans

The following rules concern the set of Booleans from B:

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| BOOL11 | H, (v = TRUE), not(v = FALSE) ⊢ Q | H ⊢ (v = TRUE) ⇒ Q |
| BOOL12 | H, (v = FALSE), not(v = TRUE) ⊢ Q | H ⊢ (v = FALSE) ⇒ Q |
| BOOL21 | H ⊢ (v = TRUE) ⇒ Q | H ⊢ (TRUE = v) ⇒ Q |
| BOOL22 | H ⊢ (v = FALSE) ⇒ Q | H ⊢ (FALSE = v) ⇒ Q |
| BOOL31 | H ⊢ (v = FALSE) ⇒ Q | H ⊢ not(v = TRUE) ⇒ Q |
| BOOL32 | H ⊢ (v = TRUE) ⇒ Q | H ⊢ not(v = FALSE) ⇒ Q |
| BOOL41 | H ⊢ (v = FALSE) ⇒ Q | H ⊢ not(TRUE = v) ⇒ Q |
| BOOL42 | H ⊢ (v = TRUE) ⇒ Q | H ⊢ not(FALSE = v) ⇒ Q |
| BOOL51 | | H ⊢ (TRUE = FALSE) ⇒ Q |
| BOOL52 | | H ⊢ not(FALSE = TRUE) ⇒ Q |

---

## Appendix A: Summary of Rules Used

### A.1 Conjunction

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| AND1 | H ⊢ ¬Q ⇒ R; H ⊢ ¬P ⇒ R | H ⊢ ¬(P ∧ Q) ⇒ R |
| AND2 | H ⊢ P ⇒ ¬Q | H ⊢ ¬(P ∧ Q) |
| AND3 | H ⊢ P ⇒ (Q ⇒ R) | H ⊢ (P ∧ Q) ⇒ R |
| AND4 | H ⊢ Q; H ⊢ P | H ⊢ P ∧ Q |
| AND5 | P ∧ ··· contains A; H ⊢ P ∧ ··· ∧ B ∧ ··· ⇒ R | H ⊢ P ∧ ··· ∧ (A ⇒ B) ∧ ··· ⇒ R |

### A.2 Disjunctions

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| OR1 | H ⊢ ¬P ⇒ (¬Q ⇒ R) | H ⊢ ¬(P ∨ Q) ⇒ R |
| OR2 | H ⊢ ¬Q; H ⊢ ¬P | H ⊢ ¬(P ∨ Q) |
| OR3 | H ⊢ Q ⇒ R; H ⊢ P ⇒ R | H ⊢ (P ∨ Q) ⇒ R |
| OR4 | H ⊢ ¬P ⇒ Q | H ⊢ P ∨ Q |

### A.3 Implications

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| IMP1 | H ⊢ P ⇒ (¬Q ⇒ R) | H ⊢ ¬(P ⇒ Q) ⇒ R |
| IMP2 | H ⊢ ¬Q; H ⊢ P | H ⊢ ¬(P ⇒ Q) |
| IMP3 | H ⊢ Q ⇒ R; H ⊢ ¬P ⇒ R | H ⊢ (P ⇒ Q) ⇒ R |
| IMP4 | H, P ⊢ Q | H ⊢ P ⇒ Q |
| IMP5 | P is in H; H ⊢ Q | H ⊢ P ⇒ Q |

| Rule | Antecedents | Consequent | Result |
|------|-------------|------------|--------|
| IMP4′ | (H, P ⊢ Q) ⇝ R | H ⊢ P ⇒ Q | P ⇒ R |

### A.4 Equivalence

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| EQV1 | H ⊢ P ⇒ (¬Q ⇒ R); H ⊢ ¬P ⇒ (Q ⇒ R) | H ⊢ ¬(P ⇔ Q) ⇒ R |
| EQV2 | H ⊢ P ⇒ ¬Q; H ⊢ ¬Q ⇒ P | H ⊢ ¬(P ⇔ Q) |
| EQV3 | H ⊢ P ⇒ (Q ⇒ R); H ⊢ ¬P ⇒ (¬Q ⇒ R) | H ⊢ (P ⇔ Q) ⇒ R |
| EQV4 | H ⊢ P ⇒ Q; H ⊢ Q ⇒ P | H ⊢ P ⇔ Q |

### A.5 Negations

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| NOT1 | H ⊢ P ⇒ R | H ⊢ ¬¬P ⇒ R |
| NOT2 | H ⊢ P | H ⊢ ¬¬P |

### A.6 Axioms

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| AXM1 | ¬P is in H | H ⊢ P ⇒ Q |
| AXM2 | P is in H | H ⊢ ¬P ⇒ Q |
| AXM3 | P is in H | H ⊢ P |
| AXM4 | R is in H | H ⊢ P ⇒ R |
| AXM5 | ¬Q is in H | H ⊢ P ⇒ (Q ⇒ R) |
| AXM6 | Q is in H | H ⊢ P ⇒ (¬Q ⇒ R) |
| AXM7 | | H ⊢ P ⇒ P |
| AXM8 | P ∧ ··· contains R | H ⊢ P ∧ ··· ⇒ R |
| AXM9 | ∀x · ¬(TRUE ∧ P) is in H; there exists E such that [x := E] P = R | H ⊢ R ⇒ Q |

### A.7 Universal Quantifications

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| ALL1 | x and y are distinct; H ⊢ ¬(∀(x, y) · P) ⇒ R | H ⊢ ¬(∀x · ∀y · P) ⇒ R |
| ALL2 | x and y are distinct; H ⊢ ¬(∀(x, y) · P) | H ⊢ ¬(∀x · ∀y · P) |
| ALL3 | x and y are distinct; H ⊢ (∀(x, y) · P) ⇒ R | H ⊢ (∀x · ∀y · P) ⇒ R |
| ALL4 | x and y are distinct; H ⊢ ∀(x, y) · P | H ⊢ ∀x · ∀y · P |
| ALL5 | x not free in R; H ⊢ ∀x · (¬P ⇒ R) | H ⊢ ¬(∀x · P) ⇒ R |
| ALL5 | x is free in R; y free in neither P nor R; S = [x := y] P; H ⊢ ∀y · (¬S ⇒ R) | H ⊢ ¬(∀x · P) ⇒ R |
| ALL6 | H ⊢ (∀x · P) ⇒ FALSE | H ⊢ ¬(∀x · P) |
| ALL7 | x not free in H; (H ⊢ P) ⇝ R; H ⊢ (♢x · R) ⇒ Q | H ⊢ (∀x · P) ⇒ Q |
| ALL7 | x is free in H; y free in neither A nor H; P = [x := y] A; (H ⊢ P) ⇝ R; H ⊢ (♢x · R) ⇒ Q | H ⊢ (∀x · A) ⇒ Q |
| ALL8 | x not free in H; H ⊢ P | H ⊢ ∀x · P |
| ALL8 | x is free in H; y free in neither P nor H; R = [x := y] P; H ⊢ R | H ⊢ ∀x · P |
| ALL9 | H, (∀x · T) ⊢ Q | H ⊢ (♡x · T) ⇒ Q |

| Rule | Antecedents | Consequent | Result |
|------|-------------|------------|--------|
| ALL7′ | x not free in H; (H ⊢ P) ⇝ R; (H ⊢ (♢x · R) ⇒ Q) ⇝ S | H ⊢ (∀x · P) ⇒ Q | S |
| ALL7′ | x is free in H; y free in neither A nor H; P = [x := y] A; (H ⊢ P) ⇝ R; (H ⊢ (♢x · R) ⇒ Q) ⇝ S | H ⊢ (∀x · A) ⇒ Q | S |
| ALL8′ | x not free in H; (H ⊢ P) ⇝ Q | H ⊢ ∀x · P | ∀x · Q |
| ALL8′ | x is free in H; y free in neither P nor H; R = [x := y] P; (H ⊢ R) ⇝ Q | H ⊢ ∀x · P | ∀y · Q |
| ALL9′ | (H, (∀x · P) ⊢ Q) ⇝ R | H ⊢ (♡x · P) ⇒ Q | (∀x · P) ⇒ R |

### A.8 Existential Quantification

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| XST1 | x and y are distinct; H ⊢ ¬(∃(x, y) · P) ⇒ R | H ⊢ ¬(∃x · ∃y · P) ⇒ R |
| XST2 | x and y are distinct; H ⊢ ¬(∃(x, y) · P) | H ⊢ ¬(∃x · ∃y · P) |
| XST3 | x and y are distinct; H ⊢ (∃(x, y) · P) ⇒ R | H ⊢ (∃x · ∃y · P) ⇒ R |
| XST4 | x and y are distinct; H ⊢ ∃(x, y) · P | H ⊢ ∃x · ∃y · P |
| XST5 | H ⊢ (∀x · ¬P) ⇒ R | H ⊢ ¬(∃x · P) ⇒ R |
| XST51 | H ⊢ (∀x · P) ⇒ R | H ⊢ ¬(∃x · ¬P) ⇒ R |
| XST6 | H ⊢ ∀x · ¬P | H ⊢ ¬(∃x · P) |
| XST61 | H ⊢ ∀x · P | H ⊢ ¬(∃x · ¬P) |
| XST7 | x not free in R; H ⊢ ∀x · (P ⇒ R) | H ⊢ (∃x · P) ⇒ R |
| XST7 | x is free in R; y free in neither P nor R; Q = [x := y] P; H ⊢ ∀y · (Q ⇒ R) | H ⊢ (∃x · P) ⇒ R |
| XST8 | x not free in H; (H ⊢ ¬P) ⇝ R; H ⊢ (∀x · R) ⇒ FALSE | H ⊢ ∃x · P |
| XST8 | x is free in H; y free in neither A nor H; P = [x := y] A; (H ⊢ ¬P) ⇝ R; H ⊢ (∀x · R) ⇒ FALSE | H ⊢ (∃x · A) |

### A.9 True and False

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| VR1 | | H ⊢ ¬TRUE ⇒ R |
| VR2 | H ⊢ FALSE | H ⊢ ¬TRUE |
| VR3 | H ⊢ R | H ⊢ TRUE ⇒ R |
| VR4 | | H ⊢ TRUE |
| FX1 | H ⊢ R | H ⊢ ¬FALSE ⇒ R |
| FX2 | | H ⊢ ¬FALSE |
| FX3 | | H ⊢ FALSE ⇒ R |

### A.10 STOP Rules

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| STOP | P is not FALSE; H ⊢ ¬P ⇒ FALSE | H ⊢ P |

| Rule | Antecedents | Consequent | Result |
|------|-------------|------------|--------|
| STOP′ | | H ⊢ P | P |

### A.11 INS Rule

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| INS | Determination of instantiations Q₁, ..., Qₙ; H ⊢ Q₁ ⇒ (Q₂ ⇒ ... (Qₙ ⇒ FALSE) ...) | H ⊢ FALSE |

### A.12 Normalisation

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| NRM1 | x not free in P; H ⊢ P ⇒ S | H ⊢ (♢x · P) ⇒ S |
| NRM2 | x not free in P; H ⊢ (P ⇒ ♢x · Q) ⇒ S | H ⊢ ♢x · (P ⇒ Q) ⇒ S |
| NRM3 | x not free in Q; Q is not FALSE; H ⊢ (Q ⇒ S) ∧ ((∀x · ¬P) ⇒ S) | H ⊢ ♢x · (P ⇒ Q) ⇒ S |
| NRM4 | x not free in Q; H ⊢ (Q ⇒ ♢x · (P ⇒ R)) ⇒ S | H ⊢ ♢x · (P ⇒ (Q ⇒ R)) ⇒ S |
| NRM5 | H ⊢ ♢x · (P ∧ Q ⇒ R) ⇒ S | H ⊢ ♢x · (P ⇒ (Q ⇒ R)) ⇒ S |
| NRM6 | H ⊢ ♢x · (R ⇒ P) ⇒ (♢x · (R ⇒ Q) ⇒ S) | H ⊢ ♢x · (R ⇒ P ∧ Q) ⇒ S |
| NRM7 | H ⊢ (♢x · P) ⇒ ((♢x · Q) ⇒ S) | H ⊢ ♢x · (P ∧ Q) ⇒ S |
| NRM8 | x and y are distinct; H ⊢ (♢(x, y) · Q) ⇒ S | H ⊢ (♢x · ∀y · Q) ⇒ S |
| NRM8 | x and y not distinct; z distinct from x and y; K = [y := z] Q; H ⊢ (♢(x, y) · K) ⇒ S | H ⊢ (♢x · ∀y · Q) ⇒ S |
| NRM9 | x and y distinct; y not free in P; H ⊢ ♢(x, y) · (P ⇒ Q) ⇒ S | H ⊢ ♢x · (P ⇒ ∀y · Q) ⇒ S |
| NRM9 | x and y not distinct or y free in P; z distinct from x, not free in P or Q; K = [y := z] Q; H ⊢ ♢(x, z) · (P ⇒ K) ⇒ S | H ⊢ ♢x · (P ⇒ ∀y · Q) ⇒ S |
| NRM10 | H ⊢ ♡x · ¬(P ∧ Q) ⇒ R | H ⊢ ♢x · (P ∧ Q ⇒ FALSE) ⇒ R |
| NRM11 | H ⊢ ♡x · ¬(TRUE ∧ P) ⇒ R | H ⊢ ♢x · (P ⇒ FALSE) ⇒ R |
| NRM12 | H ⊢ ♡x · ¬(P ∧ Q) ⇒ R | H ⊢ ♢x · (P ⇒ ¬Q) ⇒ R |
| NRM13 | H ⊢ ♡x · ¬(P ∧ ¬Q) ⇒ R | H ⊢ ♢x · (P ⇒ Q) ⇒ R |
| NRM14 | H ⊢ ♡x · ¬(TRUE ∧ P) ⇒ R | H ⊢ (♢x · ¬P) ⇒ R |
| NRM15 | H ⊢ ♡x · ¬(TRUE ∧ ¬P) ⇒ R | H ⊢ (♢x · P) ⇒ R |
| NRM16 | ∀x · P is in H | H ⊢ (♡x · P) ⇒ Q |
| NRM17 | ∀x · ¬(TRUE ∧ P) is in H; there exists E such that [x := E] P = R | H ⊢ ♡y · ¬(TRUE ∧ ¬R) ⇒ Q |
| NRM18 | ∀x · ¬(TRUE ∧ ¬P) is in H; there exists E such that [x := E] P = R | H ⊢ ♡y · ¬(TRUE ∧ R) ⇒ Q |
| NRM19 | P is in H; there exists E such that [x := E] R = P | H ⊢ ♡x · ¬(TRUE ∧ R) ⇒ Q |
| NRM20 | x not free in E; H ⊢ ♡y · ¬[x := E]P ⇒ Q | H ⊢ ♡(x, y) · ¬(P ∧ x = E) ⇒ Q |
| NRM21 | x not free in E; H ⊢ ♡y · ¬[x := E]P ⇒ Q | H ⊢ ♡(x, y) · ¬(P ∧ E = x) ⇒ Q |
| NRM22 | x not free in E; H ⊢ ¬[x := E]P ⇒ Q | H ⊢ ♡x · ¬(P ∧ x = E) ⇒ Q |
| NRM23 | x not free in E; H ⊢ ¬[x := E]P ⇒ Q | H ⊢ ♡x · ¬(P ∧ E = x) ⇒ Q |
| NRM24 | P is not of the form A ∧ B; H ⊢ ♡x · ¬(TRUE ∧ P) ⇒ Q | H ⊢ ♡x · ¬P ⇒ Q |
| NRM25 | x not free in P; H ⊢ P | H ⊢ ♡(x) · P |
| NRM26 | y not free in P; H ⊢ ♡(x, ...) · P | H ⊢ ♡(x, y, ...) · P |
| NRM27 | (xᵢ ≤ 0) and (−xᵢ ≤ 0) in (P ∧...∧ Q); R = [xᵢ := 0](P ∧...∧ Q); H ⊢ ♢(x₁,...,xᵢ₋₁,xᵢ₊₁,...,xₙ) · ¬R | H ⊢ ♡(x₁,...,xₙ) · ¬(P ∧...∧ Q) |
| NRM28 | (x ≤ 0) and (−x ≤ 0) in (P ∧...∧ Q); S = [x := 0](P ∧...∧ Q); H ⊢ ¬(S) ⇒ R | H ⊢ (♡(x) · ¬(P ∧...∧ Q)) ⇒ R |
| NRM29 | (a + xᵢ ≤ 0) and (b − xᵢ ≤ 0) in (P ∧...∧ Q); solver(a+b) = 0; S = [xᵢ := b](P ∧...∧ Q); H ⊢ ♢(...) · ¬S ⇒ R | H ⊢ (♡(x₁,...,xₙ) · ¬(P ∧...∧ Q)) ⇒ R |
| NRM29_1 | (xᵢ + a ≤ 0) and (−xᵢ + b ≤ 0) in (P ∧...∧ Q); solver(a+b) = 0; S = [xᵢ := b](P ∧...∧ Q); H ⊢ ♢(...) · ¬S ⇒ R | H ⊢ (♡(x₁,...,xₙ) · ¬(P ∧...∧ Q)) ⇒ R |
| NRM30 | (a + x ≤ 0) and (b − x ≤ 0) in (P ∧...∧ Q); solver(a+b) = 0; S = [x := b](P ∧...∧ Q); H ⊢ ¬S ⇒ R | H ⊢ (♡x · ¬(P ∧...∧ Q)) ⇒ R |
| NRM30_1 | (x + a ≤ 0) and (−x + b ≤ 0) in (P ∧...∧ Q); solver(a+b) = 0; S = [x := b](P ∧...∧ Q); H ⊢ ¬S ⇒ R | H ⊢ (♡x · ¬(P ∧...∧ Q)) ⇒ R |

### A.13 Rules on Equalities

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| EVR1 | | H ⊢ ¬(E = E) ⇒ P |
| EVR2 | H ⊢ FALSE | H ⊢ ¬(E = E) |
| EVR3 | H ⊢ P | H ⊢ (E = E) ⇒ P |
| EVR4 | | H ⊢ (E = E) |
| EVR11 | n ∈ ℕ; m ∈ ℕ; n ≠ m | H ⊢ (n = m) ⇒ P |
| EAXM1 | ¬(F = E) is in H | H ⊢ (E = F) ⇒ P |
| EAXM2 | (F = E) is in H | H ⊢ ¬(E = F) ⇒ P |
| EAXM31 | (F = E) is in H | H ⊢ (E = F) |
| EAXM32 | ¬(F = E) is in H | H ⊢ ¬(E = F) |
| EIMP51 | ¬(F = E) is in H; H ⊢ P | H ⊢ ¬(E = F) ⇒ P |
| EIMP52 | (F = E) is in H; H ⊢ P | H ⊢ (E = F) ⇒ P |
| EQC1 | H ⊢ ¬(a = c) ∨ ¬(b = d) ⇒ P | H ⊢ ¬((a, b) = (c, d)) ⇒ P |
| EQC2 | H ⊢ (a = c) ∧ (b = d) ⇒ P | H ⊢ ((a, b) = (c, d)) ⇒ P |
| EQS1 | H ⊢ E = F ⇒ R | H ⊢ eql_set(E, F) ⇒ R |
| EQS2 | H ⊢ FALSE ⇒ R | H ⊢ ¬eql_set(E, F) ⇒ R |
| EAXM91 | ∀x · ¬(TRUE ∧ p = q) is in H; there exists E such that [x := E](q = p) reduces to (a = b) | H ⊢ (a = b) ⇒ Q |
| EAXM92 | ∀x · ¬(TRUE ∧ ¬(p = q)) is in H; there exists E such that [x := E](q = p) reduces to (a = b) | H ⊢ ¬(a = b) ⇒ Q |
| OPR1 | x is a variable; x not free in H; x not free in E; Q = [x := E] P; H ⊢ Q | H ⊢ (x = E) ⇒ P |
| OPR2 | x is a variable; x not free in H; x not free in E; Q = [x := E] P; H ⊢ Q | H ⊢ (E = x) ⇒ P |
| ECTR1 | ¬Q is in H; replacing E by F in Q gives R; R is in H | H ⊢ (E = F) ⇒ P |
| ECTR2 | ¬Q is in H; replacing E by F in Q gives R; R is in H | H ⊢ (F = E) ⇒ P |
| ECTR3 | E = F is in H; replacing E by F in P gives R; R is in H | H ⊢ ¬P ⇒ Q |
| ECTR4 | F = E is in H; replacing E by F in P gives R; R is in H | H ⊢ ¬P ⇒ Q |
| ECTR5 | E = F is in H; replacing E by F in P gives R; ¬R is in H | H ⊢ P ⇒ Q |
| ECTR6 | F = E is in H; replacing E by F in P gives R; ¬R is in H | H ⊢ P ⇒ Q |

### A.14 Rules on Arithmetic

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| AR1 | H ⊢ R | H ⊢ E ≤ E ⇒ R |
| AR2 | a is numeric; b is numeric; a > b | H ⊢ a ≤ b ⇒ R |
| AR3 | H ⊢ 1 − a ≤ 0 ⇒ R | H ⊢ ¬(a ≤ 0) ⇒ R |
| AR4 | F ≤ 0 is in H; E + F > 0 | H ⊢ E ≤ 0 ⇒ R |
| AR5 | a ≤ 0 is in H; H ⊢ −a ≪ 0 ⇒ (a = 0 ⇒ R) | H ⊢ −a ≤ 0 ⇒ R |
| AR6 | −a ≤ 0 is in H; H ⊢ a ≪ 0 ⇒ (a = 0 ⇒ R) | H ⊢ a ≤ 0 ⇒ R |
| AR7 | c + b ≤ 0 is in H; a + c = 0; H ⊢ b = a ⇒ (a − b ≪ 0 ⇒ R) | H ⊢ a − b ≤ 0 ⇒ R |
| AR8 | a − b ≤ 0 is in H; a + c = 0; H ⊢ b = a ⇒ (c + b ≪ 0 ⇒ R) | H ⊢ c + b ≤ 0 ⇒ R |
| AR9 | solver(E) = F; H ⊢ F ≤ 0 ⇒ R | H ⊢ E ≤ 0 ⇒ R |
| AR10 | solver(P) = Q; H ⊢ Q ⇒ R | H ⊢ P ⇒ R |
| AR11 | | H ⊢ not(x ≤ x) ⇒ P |
| AR12 | H, (a ≤ b) ⊢ P | H ⊢ (a ≪ b) ⇒ P |

### A.15 Rules on Booleans

| Rule | Antecedents | Consequent |
|------|-------------|------------|
| BOOL11 | H, (v = TRUE), ¬(v = FALSE) ⊢ P | H ⊢ (v = TRUE) ⇒ P |
| BOOL12 | H, (v = FALSE), ¬(v = TRUE) ⊢ P | H ⊢ (v = FALSE) ⇒ P |
| BOOL21 | H ⊢ (v = TRUE) ⇒ P | H ⊢ (TRUE = v) ⇒ P |
| BOOL22 | H ⊢ (v = FALSE) ⇒ P | H ⊢ (FALSE = v) ⇒ P |
| BOOL31 | H ⊢ (v = FALSE) ⇒ P | H ⊢ ¬(v = TRUE) ⇒ P |
| BOOL32 | H ⊢ (v = TRUE) ⇒ P | H ⊢ ¬(v = FALSE) ⇒ P |
| BOOL41 | H ⊢ (v = FALSE) ⇒ P | H ⊢ ¬(TRUE = v) ⇒ P |
| BOOL42 | H ⊢ (v = TRUE) ⇒ P | H ⊢ ¬(FALSE = v) ⇒ P |
| BOOL51 | | H ⊢ (TRUE = FALSE) ⇒ P |
| BOOL52 | | H ⊢ ¬(FALSE = TRUE) ⇒ P |
