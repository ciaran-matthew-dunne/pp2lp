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
2. `make build` to check it compiles
3. `make unit-test` to run unit tests (118 tests)
4. `make test-NN` on the specific trace you're targeting

### Debugging a failing trace
1. `make test-NN` to reproduce (generates `lp/gen/trace_NN.lp`)
2. `lambdapi_check lp/gen/trace_NN.lp` for the error
3. `lambdapi_goals lp/gen/trace_NN.lp LINE` to see proof state at failure
4. Compare with the hand-written version in `lp/Traces.lp`
5. Fix in `emit_lp.ml`, rebuild, re-test

### Verifying nothing is broken
- `make unit-test` — OCaml unit tests
- `make test-each` — all 30 traces with per-trace PASS/FAIL summary
- `make test-prv FILTER=xxx` — PRV benchmark subset

## Build & Test Commands

```bash
make build                          # build OCaml parser/emitter
make unit-test                      # run OCaml unit tests (118 tests)
make test-NN                        # test single trace (e.g. make test-14)
make test-each                      # all 30 traces, summary output
make test                           # all traces in one file (fails on first error)
make prv-NAME                       # single PRV test (e.g. make prv-arith_ineq_001)
make test-prv                       # all 86 PRV replays
make test-prv FILTER=arith          # filtered PRV subset
make test-prv-each                  # per-file PRV PASS/FAIL summary
make gen-prv                        # regenerate PRV traces from .but files
```

All commands run from the **project root** (`/home/ciaran/prog/pp2lp`). Do not `cd ocaml` — the Makefile handles build directories.

## MCP Tools (lambdapi_*)

Use the `/lambdapi` skill for all Lambdapi work — it loads the MCP tools and a reference guide. Prefer MCP tools over shell `lambdapi` commands: they return structured output and are cheaper on tokens.

- `lambdapi_check file` — type-check a file. Returns OK or first error with proof context.
- `lambdapi_goals file line` — hypotheses + goals at a proof line. Essential for debugging.
- `lambdapi_try file line tactic` — test a tactic without editing. Explore before writing.
- `lambdapi_query file line query` — `compute`/`type`/`print`/`search` at a line.
- `lambdapi_symbols file` — all symbols in scope. Useful when you need a rule name.
- `lambdapi_axioms files` — audit for unproved assumptions. Run before committing.

## Token-Saving Notes

- **Never read generated LP files** (`lp/gen/`) in full — they have huge type signatures. Use `lambdapi_check` for errors and `lambdapi_goals` for proof state instead.
- **PRV replay files** (`test/prv/gen/replay/`) can be 10K+ tokens. Use `head -20` via Bash to see just the first few lines.
- **Debugging a single PRV test:** `make prv-name` generates `lp/gen/prv/name.lp` and shows the error. Then use `lambdapi_check lp/gen/prv/name.lp` and `lambdapi_goals` to inspect — don't read the generated file.
- **Prefer targeted reads.** Use `Read` with `offset`/`limit` or `Grep` rather than reading whole files. Most files in this project are small, but `emit_lp.ml` (~900 lines) and `Traces.lp` (~240 lines) benefit from targeted access.

## Current Test Status

**Traces:** 28/30 pass. **PRV benchmarks:** 6/86 pass. **OCaml unit tests:** 118 pass.

| Traces | Status | Notes |
|--------|--------|-------|
| 01–25 | PASS | Propositional, quantifier, equality |
| 26 | FAIL | OPR1 substitution fails inside nested ALL8 with 2 bound vars |
| 27 | FAIL | IMP4 continuation wraps around ∃ instead of matching it (maplet) |
| 28–30 | PASS | TRUE/FALSE/STOP |

PRV: 80 tests fail due to a mix of unimplemented INS rule (~276 occurrences), OPR1 substitution issues, and missing branching support. The conjunction associativity issue (AND3 chains) was fixed by switching to left-associative ∧ emission.

## Directory Structure

```
lp/                         Lambdapi encoding
├── B.lp                    Foundation: domain ι, membership, arithmetic (shallow encoding)
├── NonFree.lp              Stub (HOAS handles non-freeness implicitly)
├── Subst.lp                Stub (HOAS application replaces explicit substitution)
├── Proof.lp                Stub (shallow encoding uses plain functions)
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

data/
└── rules.json              PP rule catalog (arity, primed, emit args, LP status)

ocaml/                      OCaml parser and reconstruction
├── src/
│   ├── syntax_pp.ml        AST: prd, exp, line = lhs * rhs
│   ├── lexer.mll           ocamllex lexer for PP trace syntax
│   ├── parser.mly          menhir parser (entry: line_eof)
│   ├── parse_pp.ml         Driver: parse_pp_replay, parse_pp_string
│   ├── rule_db.ml          Rule metadata loaded from data/rules.json
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
- **`emit_lp.ml`** — Pretty-prints proof trees as Lambdapi. Translates PP syntax (VRAI/FAUX, `and`/`or`/`not`/`=>`) to Unicode (TRUE/FALSE, ∧/∨/¬/⇒). Conjunctions are emitted **left-associatively** (`((a ∧ b) ∧ c)`) so AND3 chains peel conjuncts correctly, even though Stdlib's `∧` notation is right-associative. AND5/AXM8 use generated `∧ₑ₁`/`∧ₑ₂`/`∧ᵢ` lambdas instead of `conj` lists.
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

All Lambdapi work must be strictly definitional. Never introduce axioms (unproved `symbol` declarations used as lemmas) without explicit permission. The only unproved symbols are:
- Domain axioms in B.lp (pair injectivity, set extensionality, arithmetic ordering)
- Admitted PP rules (AR2–AR8, AR13, EQS2) — tracked in `data/rules.json` with `lp_status: "admitted"`

## Roadmap

### Current state
- Lambdapi shallow encoding complete: all PP rules formalised with base + primed variants
- OCaml parser complete: parses all 86 PRV replays
- Rule metadata centralised in `data/rules.json`
- Automated reconstruction: 28/30 traces, 6/86 PRV

### Admitted LP rules (proved via `admit`)
- **Arithmetic** (AR2–AR8, AR13): need integer arithmetic axioms in B.lp
- **Set equality** (EQS2, EQS2_1): need `¬(eql_set E F) → ⊥` direction of set extensionality

### P0 — Unblock PRV benchmarks
1. ~~**Fix conjunction associativity**~~ — DONE. Emitter now generates left-associative ∧, AND5/AXM8 rewritten to use extraction lambdas instead of `conj` lists.
2. **Implement INS rule** — 276 occurrences in PRV replays, currently unimplemented. Takes determined instantiations Q₁…Qₙ. This is now the single biggest blocker.

### P1 — Fix remaining traces
3. **Trace 26** — OPR1 substitution predicate not generated correctly inside nested ALL8 with multi-variable bindings.
4. **Trace 27** — IMP4 continuation incorrectly wraps around existential quantifier instead of matching it directly (nested ∃ + maplet).

### P2 — Prove arithmetic rules
5. **Axiomatise integer arithmetic in B.lp** — ordering properties (antisymmetry, transitivity, strict-to-non-strict) needed to prove AR2–AR8.
6. **Prove AR2–AR8, AR13** — replace `admit` with proofs using the new axioms.

### P3 — Generalise and harden
7. **N-ary quantifier flattening** — replace ad-hoc ALL7_2, XST5_2, NRM14_2 etc. with systematic n-variable handling.
8. **Implement remaining NRM rules** — NRM10, NRM17–18, NRM21–23, NRM27–30 (arithmetic solver dispatch). Currently unused by benchmarks but needed for completeness.
9. **Incremental testing** — Makefile caching to avoid re-checking unchanged traces.

## Key References

- `doc/spec_pp.md` — Translated PP specification (rule definitions, set translator)
- `doc/b-book-ref.md` — References to Abrial's B-Book
