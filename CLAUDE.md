# CLAUDE.md

## Git Commits

Never add Co-Authored-By lines or any Claude/Anthropic attribution to commit messages.

## Project Overview

**pp2lp** translates proof traces from the Predicate Prover (PP) — an automated theorem prover used by Atelier B — into Lambdapi, a proof assistant for the lambda-Pi-calculus modulo rewriting. The goal is to independently verify PP's proofs, since PP is an untrusted oracle whose source code is not publicly available.

It also provides a round-trip pipeline: given a FOL formula, send it to PP for proving, then translate the proof back into a type-checked Lambdapi term.

## Agent Workflow

### Editing Lambdapi files (lp/)
1. Edit the `.lp` file
2. `lambdapi_check` on that file — instant feedback
3. If stuck, `lambdapi_goals file line` to see proof state, `lambdapi_try file line tactic` to experiment
4. Never guess — use MCP tools to inspect before committing to a change

### Editing OCaml code (ocaml/src/)
1. Edit the source file
2. `make build` to check it compiles
3. `make unit-test` to run unit tests
4. `make check` to verify benchmarks still pass

### Debugging a failing test
1. `make check` output shows file:line:col + full error on failure
2. `lambdapi_goals FILE LINE` to see proof state at failure
3. Fix in `emit_lp.ml`, rebuild, re-test

### Verifying nothing is broken
- `make check` — build + all synth benchmarks, halts on first **unexpected** failure. Known failures listed in `XFAIL` (Makefile) are tolerated and reported as `xfail`. Reports `trust`/`admit` counts per test and in summary.
- `make unit-test` — OCaml unit tests (standalone)

## Build & Test Commands

```bash
make check                          # build + all benchmarks, fast-fail
make check JOB=<prefix>             # filter tests by name prefix
make build                          # build OCaml parser/emitter
make unit-test                      # run OCaml unit tests
make test-NAME                      # single test (e.g. make test-and1_basic)
make prove FORMULA='...'            # send formula to PP, emit LP proof
make prove FORMULA='...' NAME=foo   # same, with custom symbol name
make gen                            # regenerate all synth goals + replays
make status                         # show test suite overview
make clean                          # remove build artifacts and generated files
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

- **Never read generated LP files** (`bench/gen/*.lp`) in full — they have huge type signatures. Use `lambdapi_check` for errors and `lambdapi_goals` for proof state instead.
- **Replay files** can be 10K+ tokens. Use `head -20` via Bash to see just the first few lines.
- **Debugging a single test:** `make test-name` generates `bench/gen/name.lp` and shows the error. Then use `lambdapi_goals` to inspect — don't read the generated file.
- **Prefer targeted reads.** Use `Read` with `offset`/`limit` or `Grep` rather than reading whole files. Most files in this project are small, but `emit_lp.ml` (~1,650 lines) and `Traces.lp` (~240 lines) benefit from targeted access.

## Current Test Status

**Synth benchmarks:** 103 goals, 103 with replays. 102/103 passing (1 failing: `all1_flatten`).

Known failures are listed in the Makefile `XFAIL` variable and tolerated by `make check`. Currently XFAIL is empty.

**Unit tests:** 153 passing.

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
├── Experiment.lp           Archived experiment (norm via rewrite rules)
├── lambdapi.pkg            Package config (pp2lp)
├── gen/                    Auto-generated .lp proofs (gitignored)
└── rules/                  PP inference rules
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
    ├── Bool.lp             §A.15 Boolean (BOOL*)
    └── Rw.lp               Rewrite lemmas for normalisation chains

ocaml/                      OCaml parser and reconstruction
├── src/
│   ├── syntax_pp.ml        AST: prd, exp, line = lhs * rhs
│   ├── lexer.mll           ocamllex lexer for PP trace syntax
│   ├── parser.mly          menhir parser (entry: line_eof)
│   ├── parse_pp.ml         Driver: parse_pp_replay, parse_pp_string
│   ├── rule_db.ml          Rule metadata (arity, primed, emit args, result schema)
│   ├── proof_tree.ml       Proof tree type + builder from line list
│   ├── emit_lp.ml          Lambdapi pretty-printer (AST → LP)
│   ├── emit_pp.ml          PP pretty-printer (AST → PP text)
│   ├── gen_but.ml          Round-trip pipeline: formula → .but → PP → LP
│   └── reconstruct.ml      Reconstruction driver: replay → .lp
├── bin/main.ml             CLI: emit/check/batch/parse/prove modes
└── test/test_pp2lp.ml      Unit + integration tests (153 tests)

bench/                      Benchmark data and pipeline
├── goals.txt               Goal definitions (NAME FORMULA per line, 103 goals)
├── gen/                    All generated output (flat dir, gitignored)
│   ├── *.but               .but files from pp2lp synth
│   ├── *.trace             .trace files from PP
│   ├── *.replay            .replay files from REPLAY
│   └── *.lp                .lp proofs from make check
├── archive/                Archived benchmarks (original traces, PRV goals)
├── gen_traces.py           Benchmark: .but → trace → replay pipeline
└── format_error.py         Lambdapi JSON error formatter
```

Dependencies: `Stdlib` → `B.lp` → `{NonFree,Subst,Proof}.lp` → `rules/*.lp` → `Traces.lp`

## Architecture

### Lambdapi encoding (`lp/`)

- **`B.lp`** — Foundation. Uses Stdlib (Prop, Set, FOL, Eq, etc.) for the shallow encoding. Domain type `ι`, membership `ϵ`, maplet `↦`, arithmetic on `τ ι` (𝟎, 𝟏, +, -, ×, ≤, ≪, —). String coercion for variables.
- **`NonFree.lp`** — Non-freeness checking (`pnf`, `enf`, `vpnf`, `venf`, `str_mem`).
- **`Subst.lp`** — Capture-avoiding substitution (`psub`, `esub`) following PP spec SUB rules.
- **Rule files (`rules/`)** — PP inference rules split by spec appendix section. Multi-premise rules (AND1, OR2, IMP3, EQV1–4, ALL7, XST8) create proof tree branching.
- **`Rw.lp`** — Rewrite lemmas for normalisation chains. Replaces the old primed (`_1`) rule mechanism: instead of separate equality-chaining symbols, the emitter uses `rewrite lemma; ...` proof scripts.
- **`Traces.lp`** — 30 hand-reconstructed PP traces as type-checked proofs.

### OCaml parser and reconstruction (`ocaml/`)

- **`syntax_pp.ml`** — AST types. `prd` (predicates), `exp` (expressions), `line = lhs * rhs`.
- **`lexer.mll`** / **`parser.mly`** — Tokenise and parse PP replay lines.
- **`proof_tree.ml`** — Builds proof tree from flat replay lines using rule arity for branching.
- **`emit_lp.ml`** — Pretty-prints proof trees as Lambdapi (~1,650 lines, largest file). Translates PP syntax (VRAI/FAUX, `and`/`or`/`not`/`=>`) to Unicode (TRUE/FALSE, ∧/∨/¬/⇒). Emits Res-typed rewrite chains as proof scripts instead of inline terms. Conjunctions are emitted **left-associatively** (`((a ∧ b) ∧ c)`) so AND3 chains peel conjuncts correctly, even though Stdlib's `∧` notation is right-associative. AND5/AXM8 use generated `∧ₑ₁`/`∧ₑ₂`/`∧ᵢ` lambdas instead of `conj` lists.
- **`emit_pp.ml`** — Reverse of the parser: converts AST back to PP text syntax. Precedence-aware to avoid unnecessary parenthesization.
- **`gen_but.ml`** — Round-trip pipeline: takes a formula, generates a `.but` file with delta conditions, calls PP (`krt`) to produce a trace, runs REPLAY, parses the replay, and emits LP.
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
- Admitted PP rules (AR3–AR8, AR9_1, AR13)

## Roadmap

### Current state
- Lambdapi shallow encoding complete: all PP rules formalised (primed `_1` rules removed, replaced by Rw.lp rewrite lemmas + Res type)
- OCaml parser complete: parses all replay formats
- Rule metadata inlined in `rule_db.ml`
- Automated reconstruction: 102/103 synth benchmarks passing (1 failing: `all1_flatten`)
- Round-trip pipeline: formula → PP → LP proof (`make prove`)
- NRM rules fully proved (0 admits in Nrm.lp)
- Eq rules fully proved (0 admits in Eq.lp)
- AR2, AR9 proved in Arith.lp
- 153 OCaml unit tests passing

### Admitted LP rules (proved via `admit`)
- **Arithmetic** (AR3–AR8, AR9_1, AR13): need integer arithmetic axioms in B.lp or encode solver-confirmed facts
- AR5/AR6 child type uses `≪` but proof needs `≤` — structural gap in rule type
- AR3/AR4/AR9_1 side conditions encoded as `π ⊤` — no recoverable information

### P1 — Reduce generated proof admits
1. **BOOL31/42 `trust` elimination** (3,400+ uses) — emitter needs to find `v ∈ BOOL` hypothesis in context
2. **INS contradiction resolution** — 62 remaining (26 fixed via ♡-hyp matching); blocked cases involve AR3_F arithmetic normalization mismatch between emitter AST and LP proof state
3. **ALL7_2 base proof admits** (~100) — needs n-ary quantifier flattening

### P2 — Prove arithmetic rules
4. **Axiomatise integer arithmetic in B.lp** — ordering properties (antisymmetry, transitivity, strict-to-non-strict) needed to prove AR5–AR8.
5. **Prove AR5–AR8, AR13** — replace `admit` with proofs using the new axioms.

### P3 — Generalise and harden
6. **N-ary quantifier flattening** — replace ad-hoc ALL7_2, XST5_2, NRM14_2 etc. with systematic n-variable handling.
7. **Incremental testing** — Makefile caching to avoid re-checking unchanged traces.

## Key References

- `doc/spec_pp.md` — Translated PP specification (rule definitions, set translator)
- `doc/b-book-ref.md` — References to Abrial's B-Book
