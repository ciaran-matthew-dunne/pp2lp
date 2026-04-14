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
4. `make test-NAME` to test a specific benchmark
5. `make check` to verify no regressions (fast-fail on first failure)

### Debugging a failing test
1. `make test-NAME` shows the error with file:line:col + proof context
2. `lambdapi_goals FILE LINE` to see proof state at failure
3. Fix the issue, rebuild, re-test
4. The failing file is in `bench/gen/NAME.lp` — prefer `lambdapi_goals` over reading it

### Verifying nothing is broken
- `make check` — build + benchmarks, halts on first **unexpected** failure. Fast.
- `make check-all` — same but reports ALL failures without stopping. Use after big changes.
- `make check JOB=fuzz` — filter to a prefix (e.g., only fuzz tests)
- `make status` — full overview: unit tests + benchmark pass/fail/empty counts
- `make unit-test` — OCaml unit tests only (153 tests)

### Typical change cycle
1. Edit OCaml code
2. `make build && make unit-test` — quick compile + unit check
3. `make test-NAME` — test specific benchmark you're working on
4. `make check` — verify no regressions before committing

## Build & Test Commands

```bash
make build                          # build OCaml parser/emitter
make unit-test                      # run OCaml unit tests (153 tests)
make check                          # build + benchmarks, fast-fail on first failure
make check-all                      # build + ALL benchmarks, report all failures
make check JOB=fuzz                 # filter tests by name prefix
make test-NAME                      # single test (e.g. make test-and1_basic)
make status                         # full overview: unit tests + benchmark counts
make prove FORMULA='...'            # send formula to PP, emit LP proof
make prove FORMULA='...' NAME=foo   # same, with custom symbol name
make gen                            # regenerate all synth goals + replays
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

## Current Test Status

**Unit tests:** 153 passing.

**Synth benchmarks:** 133 goals, 133 with replays.
- 129 passing, 3 failing, 1 skip (ill-formed replay)
- Failures: 3 are 3-variable quantifier (n-ary not yet implemented)
- Run `make status` for current counts
- Ill-formed replays (truncated traces from PP) are detected and skipped automatically
- Emission never produces `admit` — unhandled cases raise `Emit_admit` and fail cleanly

## Benchmark Pipeline

```
goals.txt  →  *.but  →  *.trace  →  *.replay  →  *.lp
 (synth)     (pp2lp)    (PP/krt)   (REPLAY)    (pp2lp emit)
```

- `make gen` runs the full pipeline (synth + trace generation)
- `make check` only runs the last step (emit + lambdapi check)
- Replays are the source of truth — they persist in `bench/gen/` (gitignored)
- `.lp` files are regenerated fresh each `make check` run

## Directory Structure

```
lp/                         Lambdapi encoding
├── B.lp                    Foundation: domain ι, membership, arithmetic (shallow encoding)
├── NonFree.lp              Stub (HOAS handles non-freeness implicitly)
├── Subst.lp                Stub (HOAS application replaces explicit substitution)
├── Proof.lp                Stub (shallow encoding uses plain functions)
├── Traces.lp               23 hand-written proof reconstructions
├── Rules.lp                Aggregates all rule modules
├── Test.lp                 Small test proofs
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
    └── Rw.lp               Rewrite lemmas for normalisation chains (_1 rules)

ocaml/                      OCaml parser and reconstruction
├── src/
│   ├── syntax_pp.ml        AST: prd, exp, binder (Bang/Forall/Forall2/Exists)
│   ├── lexer.mll           ocamllex lexer for PP trace syntax
│   ├── parser.mly          menhir parser (entry: line_eof)
│   ├── parse_pp.ml         Driver: parse_pp_replay, parse_pp_string
│   ├── rule_db.ml          Rule metadata: single rule_info record per rule
│   ├── proof_tree.ml       Proof tree type + builder from replay lines
│   ├── pp_lp.ml            LP pretty-printing (precedence-aware, conjunction helpers)
│   ├── free_vars.ml        Free variable analysis
│   ├── subst.ml            AST substitution
│   ├── hyp_ctx.ml          Hypothesis context management
│   ├── rule_args.ml        Dynamic argument emitters + variant selection + INS resolution
│   ├── emit_lp.ml          Core emission: primed chains, branching, node dispatch (~470 lines)
│   ├── emit_pp.ml          PP pretty-printer (AST → PP text)
│   ├── gen_but.ml          Round-trip pipeline: formula → .but → PP → LP
│   └── reconstruct.ml      Reconstruction driver: replay → .lp
├── bin/main.ml             CLI: emit/parse/prove/synth modes
└── test/test_pp2lp.ml      Unit + integration tests (153 tests)

bench/                      Benchmark data and pipeline
├── goals.txt               Goal definitions (NAME FORMULA per line, 133 goals)
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
- **Rule files (`rules/`)** — PP inference rules split by spec appendix section. Multi-premise rules (AND1, OR2, IMP3, EQV1–4, ALL7, XST8) create proof tree branching.
- **`Rw.lp`** — Rewrite lemmas for normalisation chains. Contains `_1` variants of rules (ALL7_1, IMP4_1, etc.) used in primed/result derivation contexts.
- **`Traces.lp`** — 23 hand-reconstructed PP traces as type-checked proofs.

### OCaml pipeline (`ocaml/`)

**Parsing:** `syntax_pp.ml` → `lexer.mll` → `parser.mly` → `parse_pp.ml`

**Tree building:** `proof_tree.ml` builds proof trees from flat replay lines. Key concepts:
- **Base vs Primed context:** `_1`-suffixed rules form "result derivations" inside ALL7/XST8
- **`collect_primed`:** Scans ahead to find ALL7/XST8, collects _1 chain
- **`build_postorder`:** Stack-based post-order tree construction for primed subtrees
- **`replay_arity`:** Strips `_1` suffix to look up base rule arity (XST8_1 is special: arity 1)

**Emission:** `emit_lp.ml` (core, ~470 lines) + helpers in extracted modules:
- `pp_lp.ml` — LP pretty-printing with binding power tracking
- `free_vars.ml` — Free variable collection
- `hyp_ctx.ml` — Hypothesis context threading
- `rule_args.ml` — Per-rule argument emitters, variant selection, INS resolution, result computation

### PP Replay Format

Replay lines: `[RULE] <goal>` or `[RULE(arg)] <goal>` or `[FIN(result)] <FIN(...)>`

Rules applied backwards (bottom-up from goal). Multi-premise rules cause branching (depth-first). Special entries:
- `[FIN(...)]` — normalisation boundary, carries result predicate
- `[STOP_NORM]`, `[NRM]` — phantom entries (arity -1), skipped
- `[RULE_1]` — primed rule in result derivation (first antecedent of ALL7/XST8)
- Non-_1 NRM steps between _1 rules and FIN — normalisation bookkeeping, not proof steps

## Roadmap

### Current state
- Lambdapi shallow encoding complete: all PP rules formalised
- OCaml pipeline: 13 modules in ocaml/src/ (emit_lp.ml ~470 lines)
- 129/133 synth benchmarks passing (~97%), 153 unit tests
- Round-trip pipeline: formula → PP → LP proof (`make prove`)
- NRM rules mostly proved (3 admits remain in Nrm.lp: NRM10, NRM11, NRM18)
- Eq rules fully proved (0 admits in Eq.lp)
- Ill-formed replays detected and skipped automatically (exit code 2)

### Admitted LP rules (proved via `admit`)
- **Arithmetic** (AR2–AR8, AR13): need integer arithmetic axioms in B.lp
- **Normalisation** (NRM10, NRM11, NRM18): ♡/♢ binder equivalences

### P1 — Prove arithmetic rules
1. **Axiomatise integer arithmetic in B.lp** — ordering properties needed for AR5–AR8
2. **Prove AR5–AR8, AR13** — replace `admit` with proofs

### P2 — Generalise and harden
3. **N-ary quantifier flattening** — 3+ variable handling for ALL7_3, XST8_3 (3 failing tests)
4. **INS unification** — INS resolution fails on some multi-variable membership contexts (1 admit in xst8_2_mem)
5. **Incremental testing** — Makefile caching to avoid re-checking unchanged traces

## Key References

- `doc/spec_pp.md` — Translated PP specification (rule definitions, set translator)
- `doc/b-book-ref.md` — References to Abrial's B-Book
