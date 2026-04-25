# CLAUDE.md

**On a fresh session, invoke `/pp2lp` first** — it loads source-layout
pointers, debugging workflows, and the emitter dispatch reference.
This file is the durable conventions; the skill is the how-to layer.

## Project

**pp2lp** translates Predicate Prover (PP) proof traces (Atelier B's automated prover) into Lambdapi so they can be independently type-checked. Also offers a round-trip: `formula → PP → type-checked Lambdapi term`.

Source layout (rediscoverable via `ls`): `lp/` Lambdapi encoding, `ocaml/src/` pipeline, `bench/{claude,claude-arith,prv,og,fuzz}/` benchmarks, `doc/` spec and references.

## Commits

Never include Co-Authored-By, or Claude/Anthropic attribution.

## Workflow

**Editing `lp/**/*.lp`** — for one-shot probes prefer `pp2lp lp-probe FILE LINE 'COMMAND;'` (covers compute / type / print / in-proof print / proofterm); for batch audits use `pp2lp lp-check` / `pp2lp lp-axioms`; for scoped trace use `pp2lp lp-debug FILE --flags=u --at=L`. Use the `/lambdapi` skill (MCP) for the interactive `lambdapi_try` loop where a warm LSP session helps. Avoid reading generated `bench/*/*.lp` — they're huge.

**Editing `ocaml/src/**`** — `make build` for compile check; `make test-NAME` for one benchmark (bypasses cache); `make check` for full regression.

**Adding goals** — `bench/claude/goals.txt`. Test one with `make prove FORMULA='...'` before committing. Then `make test-NAME`; `make check` at the end. See "PP limitations" below before writing.

## Commands

Everything orchestration runs through the `pp2lp` OCaml CLI. The Makefile
is now a thin shim of one-liners; both forms work.

```
# Building
make build                          # alias for: cd ocaml && dune build

# Running suites
pp2lp check    [--suite=X] [--job=PFX] [--name=Y] [--fresh] [--all-failures] [--json]
pp2lp status   [--suite=X]
pp2lp coverage [--by-suite] [--missing]
pp2lp gen      [--suite=X] [--alloc=...] [--all]
pp2lp clean    [--lpo] [--cache] [--all] [--suite=X]

# Emission / round-trip (existing surface, now with --json on emit)
pp2lp emit  REPLAY... [-trace] [--json]
pp2lp parse REPLAY... [-v]
pp2lp prove FORMULA   [--name NAME]
pp2lp synth GOALS DIR

# Debugging — new in this revision
pp2lp debug REPLAY    [--show=dispatch|tree|both]
pp2lp show-fail SUITE NAME       # decode .cache/<NAME>.fail
pp2lp diff REPLAY                # side-by-side PP rule sequence vs LP

# Lambdapi tooling (file-level; MCP keeps lambdapi_try / lambdapi_symbols)
pp2lp lp-check FILE...                  [--json] [--all-errors]
pp2lp lp-axioms FILE...                 [--scope=file|project] [--json]
pp2lp lp-probe FILE LINE 'COMMAND;'     [--raw]
pp2lp lp-debug FILE --flags=FLAGS [--at=L] [--end-at=L] [--save-to=PATH] [--raw]

# Make aliases (all forward to pp2lp ...)
make check [SUITE=X] [JOB=P]
make check-all [SUITE=X]                  # --all-failures
make check-fresh [SUITE=X]                # --fresh + --all-failures
make check-{claude,claude-arith,prv,og,fuzz}
make test SUITE=X NAME=Y                  # single test, bypasses cache
make test-NAME                            # ≡ test SUITE=claude NAME=NAME
make test-cache                           # OCaml unit tests for the cache module
make status, make coverage
make gen [SUITE=X] [ALLOC=...]
make gen-{claude,claude-arith,prv,fuzz}, make gen-all
make prove FORMULA='...' [NAME=foo]
make clean-lpo, make clean
```

Run from project root.

## Harness automation

A `PostToolUse` hook in `.claude/settings.local.json` clears `lp/**/*.lpo` and `bench/*/.cache` whenever you edit LP rules or OCaml source. This avoids "File X.lpo is incompatible with current binary" errors and stale cache hits after signature changes. If you still see that error, `make clean-lpo`.

## Caching

`pp2lp check` skips tests whose `bench/<suite>/.cache/<name>.{ok,fail,skip}`
marker is newer than both the `.replay` and a sentinel (newest of `pp2lp`
binary + any `lp/**/*.lp`). The hook above handles normal invalidation;
`pp2lp check --fresh` (or `make check-fresh`) forces. Cache logic lives
in `ocaml/src/cache.ml`; regression tests in `ocaml/test/test_cache.ml`
(`make test-cache`).

`.ok` body is `"<trust> <admit>"` for status accounting. `.fail` body
is the raw lambdapi output (NDJSON when supported). `.skip` body is a
short reason string. The on-disk format hasn't changed — caches written
by previous Make-based runs remain valid.

## Lambdapi tools — pp2lp vs MCP split

**File-level (pp2lp, no LSP roundtrip):**
- `pp2lp lp-check FILE...` — type-check, parses NDJSON diagnostics
- `pp2lp lp-axioms FILE...` — assumptions / admits / rewrite rules.
  Use `--scope=project` to follow `require` within the project. Run
  before committing to audit unproved assumptions.
- `pp2lp lp-probe FILE LINE 'COMMAND;'` — generic primitive: writes
  a sibling probe file with COMMAND inserted at LINE, runs `lambdapi
  check`, returns the relevant output. Covers what `lambdapi_query`,
  `lambdapi_goals`, `lambdapi_proofterm` do via LSP. Examples:
    `compute TERM;`, `type TERM;`, `print SYMBOL;` (toplevel)
    `print;`, `proofterm;`            (in-proof tactics)
- `pp2lp lp-debug FILE --flags=FLAGS [--at=L] [--end-at=L]` — inserts
  `debug +FLAGS;` / `debug -FLAGS;` toggles in a probe file so
  lambdapi *only emits* debug for the bracketed region. Output is
  bounded by construction. The trace lives on stderr; command echoes
  on stdout. `--save-to=PATH` for full capture.

**LSP-backed (MCP, agent-driven probes):**
- `lambdapi_check FILE` — type-check, returns first error with context
- `lambdapi_try FILE LINE TACTIC` — test a tactic without editing
  (the *interactive* probe loop; benefits from a warm LSP session)
- `lambdapi_symbols FILE` — symbols in scope (LSP uses elaborated
  state to surface imports etc.)

The split: anything that can be expressed as "insert a Lambdapi
command at line N and read the result" goes in pp2lp via `lp-probe`
(or `lp-debug` for trace flags). It's deterministic, line-precise,
runs in CI, and doesn't require a running LSP. The MCP keeps the
agent-driven `try` loops where the LSP keeps elaborated context warm
across many probes.

## PP Limitations (read before writing goals)

- **BOOL membership**: PP cannot reason about `a: BOOL` abstractly. Use `btrue`/`bfalse` only as concrete terms in equalities.
- **Arithmetic**: PP proves arithmetic goals; LP rules (AR1–AR13) reduce to `B.lp`'s integer primitives. Some emitted bench proofs carry `trust` for solver-level conjuncts. Audit with `pp2lp lp-axioms lp/rules/Arith.lp`.
- **Cascaded `=>`**: PP's `=>` is left-associative. `(p => q) => (r => s) => g` parses as `((p => q) => (r => s)) => g`. Use `and` to conjoin independent hypotheses.
- **Set-theoretic surface**: `eql_set`, pair decomposition, higher-order set operators aren't in the goal formula syntax.
- **Trust axioms are expected in prv**: the Atelier B corpus legitimately exercises solver-level reasoning and documented PP→LP semantic gaps (OPR1, arithmetic AC, REPLAY truncation). `make check-all SUITE=prv` reports trust counts.

## Suites

Run `pp2lp status` for current pass/fail/skip/trust counts.

- **claude** — iteration surface. AI-generated goals from `bench/claude/goals.txt`. Should stay at 0 failures.
- **claude-arith** — AI-generated arithmetic goals (§A.14 AR-rule coverage). Some emitted proofs carry `trust` for solver-level conjuncts.
- **prv** — Atelier B Proof Rules Validator corpus. Set-theoretic proof obligations; many need trust rewrites. Not a regression target.
- **og** — frozen pre-baked `.replay` files (no `.but` source). Legacy.
- **fuzz** — placeholder for a random-formula generator.

## Admitted / trust — categories

For the *current* set of admits + assumptions, run
`pp2lp lp-axioms lp/rules/*.lp lp/B.lp` (or `--scope=project` to
follow `require`). The categories below are stable; the line numbers
and counts are not.

- **`lp/B.lp` constants** — B-Book primitives (carrier types, set
  membership, bool/pair/integer primitives, `≤`). Intentional axioms.
- **`lp/rules/Rw.lp` admits** — one-point-rule substitution inside the
  `_1` chain (OPR1_1 / OPR2_1). Only the ← direction of the
  biconditional holds, so admitted pointwise. The known soundness gap.
- **Emitted `trust` in bench output** — three kinds, see emitter trace
  tags (`pp2lp emit -trace`):
  - NRM20–23 subtree close (HOU blocker after λ-applied form)
  - INS arithmetic-match conjuncts (solver equality bridge)
  - OPR1/OPR2 primed bridge in the `_1` chain

Per-test trust + admit counts are in the suite cache; surface them
with `pp2lp status` or the per-test `warn` lines from `pp2lp check`.

## Replay format (quick reference)

Lines: `[RULE] <goal>` | `[RULE(arg)] <goal>` | `[FIN(result)] <FIN(...)>`. Rules applied backwards; multi-premise rules branch DFS. Special: `[FIN]` carries normalisation result; `[STOP_NORM]`, `[NRM]` are phantoms (skipped); `[RULE_1]` is primed (inside ALL7/XST8 result chain); non-_1 NRM between _1 and FIN is bookkeeping.

## References

- `doc/spec_pp.md` — PP specification (translated)
- `doc/pp_rules.md` — rule-by-rule summary
- `doc/b-book-ref.md` — Abrial's B-Book pointers
