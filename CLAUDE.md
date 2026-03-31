# CLAUDE.md

## Git Commits

Never add Co-Authored-By lines or any Claude/Anthropic attribution to commit messages.

## Project Overview

**pp2lp** translates proof traces from the Predicate Prover (PP) — an automated theorem prover used by Atelier B — into Lambdapi, a proof assistant for the lambda-Pi-calculus modulo rewriting. The goal is to independently verify PP's proofs, since PP is an untrusted oracle whose source code is not publicly available.

## Agent Workflow

### Editing Lambdapi files (lp/)
1. Edit the `.lp` file
2. `lambdapi_check` on that file — instant feedback
3. If stuck, `lambdapi_goals file line` to see proof state, `lambdapi_try file line tactic` to experiment
4. Never guess — use MCP tools to inspect before committing to a change

### Editing OCaml code (ocaml/src/)
1. Edit the source file
2. `cd ocaml && dune build` to check it compiles
3. `cd ocaml && dune test` to run unit tests (~500 tests)
4. `make test-NN` on the specific trace you're targeting

### Debugging a failing trace
1. `make test-NN` to reproduce (generates `lp/gen/trace_NN.lp`)
2. `lambdapi_check lp/gen/trace_NN.lp` for the error
3. `lambdapi_goals lp/gen/trace_NN.lp LINE` to see proof state at failure
4. Compare with the hand-written version in `lp/Traces.lp`
5. Fix in `emit_lp.ml`, rebuild, re-test

### Verifying nothing is broken
- `cd ocaml && dune test` — OCaml correctness
- `make test-each` — all 30 traces with per-trace PASS/FAIL summary
- `make test-prv FILTER=xxx` — PRV benchmark subset

## Build & Test Commands

```bash
cd ocaml && dune build              # build OCaml parser/emitter
cd ocaml && dune test               # run unit tests
make test-NN                        # test single trace (e.g. make test-14)
make test-each                      # all 30 traces, summary output
make test                           # all traces in one file (fails on first error)
make test-prv                       # all 86 PRV replays
make test-prv FILTER=arith          # filtered PRV subset
make gen-prv                        # regenerate PRV traces from .but files
```

## MCP Tools (lambdapi_*)

Prefer these over shell commands for all Lambdapi work.

- `lambdapi_check file` — type-check a file. Returns OK or first error with proof context.
- `lambdapi_goals file line` — hypotheses + goals at a proof line. Essential for debugging.
- `lambdapi_try file line tactic` — test a tactic without editing. Explore before writing.
- `lambdapi_query file line query` — `compute`/`type`/`print`/`search` at a line.
- `lambdapi_symbols file` — all symbols in scope. Useful when you need a rule name.
- `lambdapi_axioms files` — audit for unproved assumptions. Run before committing.

## Current Test Status

| Traces | Status | Notes |
|--------|--------|-------|
| 01–25 | PASS | Propositional, quantifier, equality |
| 26 | FAIL | Missing subproofs — XST8 reconstruction with nested quantifiers |
| 27 | FAIL | Unification error — nested ∃ with maplet |
| 28–30 | PASS | TRUE/FALSE/STOP |

28/30 traces pass. OCaml tests: 509 tests, all pass.

## Directory Structure

```
lp/                         Lambdapi encoding
├── B.lp                    Foundation: Prd, Exp, Var (shallow encoding using Stdlib)
├── Eq.lp                   Syntactic equality rewrite rules
├── NonFree.lp              Non-freeness checking
├── Subst.lp                Capture-avoiding substitution
├── Proof.lp                (Mostly empty in shallow encoding)
├── Interp.lp               Semantic interpretation (soundness bridge)
├── Traces.lp               30 hand-written proof reconstructions
├── Rules.lp                Aggregates all rule modules
├── Test.lp                 Small test proofs
├── lambdapi.pkg            Package config (pp2lp)
├── gen/                    Auto-generated .lp proofs (gitignored)
└── rules/                  PP inference rules (base + primed _1 variants)
    ├── Conj.lp             §A.1  Conjunction (AND1–5)
    ├── Disj.lp             §A.2  Disjunction (OR1–4)
    ├── Impl.lp             §A.3  Implication (IMP1–5)
    ├── Equiv.lp            §A.4  Equivalence (EQV1–4)
    ├── Neg.lp              §A.5  Negation (NOT1–2)
    ├── Axm.lp              §A.6  Axioms (AXM1–9, AXM9c)
    ├── All.lp              §A.7  Universal quantification (ALL1–9)
    ├── Xst.lp              §A.8  Existential quantification (XST1–8)
    ├── TrueFalse.lp        §A.9–11  TRUE/FALSE/STOP/INS
    ├── Nrm.lp              §A.12 Normalisation (NRM1–30)
    ├── Eq.lp               §A.13 Equality (EVR, OPR, EAXM, EQC, EQS, ECTR)
    ├── Arith.lp            §A.14 Arithmetic (AR1–13)
    └── Bool.lp             §A.15 Boolean (BOOL*)

ocaml/                      OCaml parser and reconstruction
├── src/
│   ├── syntax_pp.ml        AST: prd, exp, line = lhs * rhs
│   ├── lexer.mll           ocamllex lexer for PP trace syntax
│   ├── parser.mly          menhir parser (entry: line_eof)
│   ├── parse_pp.ml         Driver: parse_pp_replay, parse_pp_string
│   ├── proof_tree.ml       Proof tree type + builder from line list
│   ├── emit_lp.ml          Lambdapi pretty-printer
│   └── reconstruct.ml      Reconstruction driver: replay → .lp
├── bin/main.ml             CLI: parse/emit-lp modes
└── test/test_pp2lp.ml      Unit + integration tests

test/
├── traces/                 30 hand-written traces + replays (01–30)
├── prv/                    123 PRV proof goals (.but files)
│   └── gen/                Generated output (gitignored)
└── gen_traces.py           Benchmark: .but → trace → replay pipeline
```

Dependencies: `Stdlib` → `B.lp` → `{Eq,NonFree,Subst,Proof,Interp}.lp` → `rules/*.lp` → `Traces.lp`

## Architecture

### Lambdapi encoding (`lp/`)

- **`B.lp`** — Foundation. Uses Stdlib (Prop, Set, FOL, Eq, etc.) for the shallow encoding. Domain type `ι`, membership `ϵ`, maplet `↦`, arithmetic on `τ ι` (𝟎, 𝟏, +, -, ×, ≤, ≪, —). String coercion for variables.
- **`Eq.lp`** — Sequential rewrite rules for syntactic equality (`str_eq`, `var_eq`, `exp_eq`, `prd_eq`).
- **`NonFree.lp`** — Non-freeness checking (`pnf`, `enf`, `vpnf`, `venf`, `str_mem`).
- **`Subst.lp`** — Capture-avoiding substitution (`psub`, `esub`) following PP spec SUB rules.
- **`Interp.lp`** — Semantic interpretation. `sat` maps predicates to propositions, `den` maps expressions to denotations.
- **Rule files (`rules/`)** — PP inference rules split by spec appendix section. Each rule has a base form and a primed `_1` variant for result-producing trace reconstruction. Multi-premise rules (AND1, OR2, IMP3, EQV1–4, ALL7, XST8) create proof tree branching.
- **`Traces.lp`** — 30 hand-reconstructed PP traces as type-checked proofs.

### OCaml parser and reconstruction (`ocaml/`)

- **`syntax_pp.ml`** — AST types. `prd` (predicates), `exp` (expressions), `line = lhs * rhs`.
- **`lexer.mll`** / **`parser.mly`** — Tokenise and parse PP replay lines.
- **`proof_tree.ml`** — Builds proof tree from flat replay lines using rule arity for branching.
- **`emit_lp.ml`** — Pretty-prints proof trees as Lambdapi. Translates PP syntax (VRAI/FAUX, `and`/`or`/`not`/`=>`) to Unicode (TRUE/FALSE, ∧/∨/¬/⇒).
- **`reconstruct.ml`** — Wires parse → tree → emit.

## PP Trace Format

Raw trace: `[AXM1] & [NOT1] & [OR4] & ... & (not(p and q) => not(p) or not(q))`

Replay expands into per-step lines:
```
[AND1] <not(p and q) => not(p) or not(q)>
[IMP4] <not(q) => not(p) or not(q)>
...
```

Rules applied backwards (bottom-up from goal). Multi-premise rules cause branching (left-to-right, depth-first). `[FIN(...)]` = normalisation boundary (not a rule). `[STOP_NORM]` and bare `[NRM]` = phantom entries to skip.

## Critical: No Axioms

All Lambdapi work must be strictly definitional. Never introduce axioms (unproved `symbol` declarations used as lemmas) without explicit permission. The only unproved symbols are the PP inference rules themselves (deep encoding layer) — not logical axioms.

## Roadmap

### Current state
- Lambdapi encoding complete: all PP rules formalised with base + primed variants
- OCaml parser complete: parses all 86 PRV replays successfully
- Automated reconstruction: 28/30 traces pass, 2 fail (traces 26, 27)

### Next
1. Fix traces 26–27 (nested quantifier/maplet reconstruction)
2. Extended rules: equality, arithmetic, boolean against 86 PRV replays
3. Polish: batch mode, error handling, verification suite

## Key References

- `doc/spec_pp.md` — Translated PP specification (rule definitions, set translator)
- `doc/b-book-ref.md` — References to Abrial's B-Book
