-----------------------------------------
# Translating PP Proof Traces to LambdaPi.
-----------------------------------------

The Predicate Prover (PP) is an automated theorem used by Atelier B.

PP is an *oracle*; results are trusted by Atelier-B.
The source code for PP is not publicly available.

# Obtaining Traces from PP.

Assume that we have `PP.kin` on path.
To obtain the trace of formula encoded in `phi.goal`, we run:
```bash
krt -b PP.kin phi.goal
```
This creates `phi.trace` with the following contents:
```
﻿ [AXM1] &
 [NOT1] &
 [OR4] &
 [IMP4] &
 [AXM4] &
 [OR4] &
 [IMP4] &
 [AND1] &
  (not(p and q) => not(p) or not(q))
```
Each `[<string>]` is a *rule*, and the *goal* is given in
the final line as `(<string>)`.

The trace can be understood as a *backwards* derivation,
where we begin with the goal; applying rules from bottom-to-top.
Because some rules have more than one premise, rule application
is performed left-to-right, depth-first.
For example, see the `lambdapi` encoding of the proof trace:
```lambdapi
symbol {|01.trace|} [p q : El prd] :
  Thm (not (p and q) => ((not p) or (not q))) ≔
begin
  assume p q;
  apply AND1
  {
    apply IMP4;
    apply OR4;
    apply AXM4
  } {
    apply IMP4;
    apply OR4;
    apply NOT1;
    apply AXM1
  }
end;
```

### PP's Proof System

The rules of PP are documented in `pp-trace-manref.pdf`.

<!--definition-->
Define `idt` as the set of *identifiers*, and `vrb` as the
set of *variable bindings* thus:
```
 x ⦂ idt ⩴ <string>
vs ⦂ vrb ≔ list idt
```
<!--end-->

<!--definition-->
Let `prd` be the set of *predicates* defined by the
following rules, where `φ, ψ ⦂ frm` are *formulas*
and `X,Y,Z ⦂ exp` are *expressions*.
```
P,Q,R ⦂ prd ⩴
  ∣ P ∧ Q ∣ P ∨ Q ∣ P ⟹ Q ∣ P ⟺ Q ∣ ¬ P
  ∣ ∀ vs ⋅ P ∣ ∃ vs ⋅ P ∣ X = Y ∣ φ
```
Formulas and expressions may use 'external'
function/relation symbols and also may contain variables
bound by `∀` and `∃`.

A *term* `t` is either an expression, formula, or predicate.
Equality on terms is written written `t == t'`.
Terms are NOT considered equal up to α-conversion.
<!--end-->

<!--definition-->
Assume a definition of *free variable* on `exp` and `frm`.
- Extend this definition to `prd` in the "obvious" way.
- Extend this definition to `list prd`.
<!--end-->

<!--definition-->
Assume a definition of capture-avoiding *substitution*
on `exp` and `frm`. Extend this definition to predicates
in the "obvious" way.

Use the following (prefix) notation:
  `[x ≔ E](t)`,
where `x` is a variable, `E` is an expression,
and `t` is either a formula, expression, or predicate.
<!---->


## Sequents and Inference Rules.

<!--definition-->
A *sequent* is an expression `Σ` of the form `H ⟝ P`,
where `H` is a list of predicates called the *hypothesis*
and `P` is a predicate called the *conclusion*.
<!--end-->

<!--definition-->
A *resultant* is an expression `T` of the form `Σ ⟿ P`
for some sequent `Σ` and some predicate `P`.
<!--end-->

<!--definition-->
An *inference* is an expression `ι` with one of the
following forms, called *sequent inferences* and
*resultant inferences* respectively:
```
  ι ⦂ inf ⩴
    | {T_1,...,T_n, Σ_1,...,Σ_m} ⇛ Σ
    | {T_1,...,T_n} ⇛ T
```
In either case, the members of the list(s) on the left-side
of `⇛` are called *inputs*, and the sequent/resultant on
the right-side is called the *output*.

The inputs of sequent inferences are either resultants
or sequents, and the inputs of a resultant inference are
always resultants.
<!--end-->

<!--definition-->
We can view the *inference rules* of PP as defining
(infinite) sets of inferences by set-comprehension,
which allows for side-conditions. e.g.;

Let `IMP5` be the set of inferences of the form:
  `(H ⟝ P) ⇛ (H ⟝ P ⟹ Q)`
where `P` and `Q` are predicates and `H` is a list of
predicates such that `P ⋿ H`.
Or more formally:
`IMP5 ≔
  {
    (H ⟝ P) ⇛ (H ⟝ P ⟹ Q)
  ∣
    H ∈ list prd, P,Q ∈ prd, P ∈ |H|
  }`
<!--end-->

<!--definition-->
A *derivation* is a well-founded tree `(Δ, ε, ℓ)`
with a set `V` of vertices, an edge function `ε : Δ → 𝒫(Δ)`,
and a labelling function `ℓ : Δ → (seq ∪ res)`.

A derivation `Δ` is *valid* wrt. a set of inferences `R` iff
for each `v ∈ Δ` the inference `{ℓ(w_1)...ℓ(w_n)} ⇛ ℓ(v)`
belongs to `R`, where `{w_1,...,w_n} = ε(v)`.
<!--end-->




<!--todo:
  lambdapi encoding of syntax,
  lambdapi encoding of rules, side conditions, .... -->




### Replaying Proof Traces.

We can also obtain a 'replay' thus:
```bash
krt -b REPLAY.kin replay.goal
```
where `replay.goal` is a file pointing to `phi.trace`:
```
Flag(FileOn("replay.res")) & ("phi.trace")
```
