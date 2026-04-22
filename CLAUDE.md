# CLAUDE.md

## Project

**pp2lp** translates Predicate Prover (PP) proof traces (Atelier B's automated prover) into Lambdapi so they can be independently type-checked. Also offers a round-trip: `formula → PP → type-checked Lambdapi term`.

Source layout (rediscoverable via `ls`): `lp/` Lambdapi encoding, `ocaml/src/` pipeline, `bench/{claude,prv,og,fuzz}/` benchmarks, `doc/` spec and references.

## Commits

Never include Co-Authored-By, or Claude/Anthropic attribution.

## Workflow

**Editing `lp/**/*.lp`** — use the `/lambdapi` skill. Prefer `lambdapi_check`, `lambdapi_goals FILE LINE`, `lambdapi_try FILE LINE TACTIC` over Bash `lambdapi` and over reading generated `bench/*/*.lp`. The latter are huge.

**Editing `ocaml/src/**`** — `make build` for compile check; `make test-NAME` for one benchmark (bypasses cache); `make check` for full regression.

**Adding goals** — `bench/claude/goals.txt`. Test one with `make prove FORMULA='...'` before committing. Then `make test-NAME`; `make check` at the end. See "PP limitations" below before writing.

## Commands

```
make build                   # compile OCaml
make check [SUITE=X] [JOB=P] # run suite X (default prv); filter tests by prefix P
make check-all [SUITE=X]     # report ALL failures instead of fast-fail
make check-fresh [SUITE=X]   # drop .lpo + .cache, then check-all
make check-{claude,prv,og,fuzz}
make test-NAME               # single claude test, no cache
make status                  # per-suite counts from cache (fast)
make prove FORMULA='...' [NAME=foo]  # round-trip a goal
make gen [SUITE=X]           # regenerate .but → .trace → .replay (incremental)
make gen-{claude,prv,fuzz}
make coverage                # per-suite × per-rule hit matrix
make clean-lpo               # drop stale Lambdapi object files
make clean                   # full reset
```

Run from project root; the Makefile handles `ocaml/` build dirs.

## Harness automation

A `PostToolUse` hook in `.claude/settings.local.json` clears `lp/**/*.lpo` and `bench/*/.cache` whenever you edit LP rules or OCaml source. This avoids "File X.lpo is incompatible with current binary" errors and stale cache hits after signature changes. If you still see that error, `make clean-lpo`.

## Caching

`make check` and `make gen` skip tests whose `bench/<suite>/.cache/<name>.{ok,fail,skip}` marker is newer than both the `.replay` and a sentinel (newest of `pp2lp` binary + any `lp/**/*.lp`). The hook above handles normal invalidation; `check-fresh` forces.

## MCP tools (Lambdapi)

Prefer these over shell `lambdapi`:
- `lambdapi_check FILE` — type-check, returns first error with context
- `lambdapi_goals FILE LINE` — hypotheses + goals at line
- `lambdapi_try FILE LINE TACTIC` — test a tactic without editing
- `lambdapi_query FILE LINE QUERY` — `compute`/`type`/`print`/`search`
- `lambdapi_symbols FILE` — symbols in scope
- `lambdapi_axioms FILES` — audit unproved assumptions (run before committing)

## PP Limitations (read before writing goals)

- **BOOL membership**: PP cannot reason about `a: BOOL` abstractly. Use `btrue`/`bfalse` only as concrete terms in equalities.
- **Arithmetic**: PP proves arithmetic goals but AR2–AR8/AR13 use `admit` in LP (no integer axioms in `B.lp` yet). Round-trip works; LP proofs aren't fully checked.
- **Cascaded `=>`**: PP's `=>` is left-associative. `(p => q) => (r => s) => g` parses as `((p => q) => (r => s)) => g`. Use `and` to conjoin independent hypotheses.
- **Set-theoretic surface**: `eql_set`, pair decomposition, higher-order set operators aren't in the goal formula syntax.
- **Trust axioms are expected in prv**: the Atelier B corpus legitimately exercises solver-level reasoning and documented PP→LP semantic gaps (OPR1, arithmetic AC, REPLAY truncation). `make check-all SUITE=prv` reports trust counts.

## Suites

- **claude** — iteration surface. AI-generated goals from `bench/claude/goals.txt`. Should stay at 0 failures.
- **prv** — Atelier B Proof Rules Validator corpus. Set-theoretic proof obligations; many need trust rewrites. Not a regression target.
- **og** — frozen pre-baked `.replay` files (no `.but` source). Legacy.
- **fuzz** — placeholder for a random-formula generator.

## Admitted / trust status (as of last check)

Audit with `lambdapi_axioms ["lp/rules/*.lp"]`:

- **Arith.lp**: AR2–AR8, AR13 — integer arithmetic not formalised.
- **Rw.lp**: OPR1_1, OPR2_1 — one-point-rule substitution inside the _1 chain; only the ← direction of the biconditional holds, so admitted pointwise.
- **Emitted trust in prv**: NRM20–23 subtree close (HOU blocker), INS arithmetic-match conjuncts, OPR1/OPR2 primed bridge.
- **Everything else**: provable. Run `make check-all SUITE=prv` to see current counts (last run: 53 pass, 17 fail, 30 skip [3238 trust]).

## Replay format (quick reference)

Lines: `[RULE] <goal>` | `[RULE(arg)] <goal>` | `[FIN(result)] <FIN(...)>`. Rules applied backwards; multi-premise rules branch DFS. Special: `[FIN]` carries normalisation result; `[STOP_NORM]`, `[NRM]` are phantoms (skipped); `[RULE_1]` is primed (inside ALL7/XST8 result chain); non-_1 NRM between _1 and FIN is bookkeeping.

## References

- `doc/spec_pp.md` — PP specification (translated)
- `doc/pp_rules.md` — rule-by-rule summary
- `doc/b-book-ref.md` — Abrial's B-Book pointers
