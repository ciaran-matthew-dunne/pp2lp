# CLAUDE.md

Maintainer notes for **pp2lp** — translates Atelier B Predicate Prover
(PP) proof traces to Lambdapi for independent type-checking. Round-trip:
`formula → PP → type-checked Lambdapi term`.

This is the maintainer worktree. Heavy agent experimentation happens in
`../worktrees/pp2lp/...`. Tooling that exists primarily to help an agent
verify its own work belongs there, not here.

## Layout

`lp/` Lambdapi encoding · `ocaml/src/` pipeline · `ocaml/bin/main.ml` CLI ·
`bench/{prv,og}/` benchmarks · `doc/` spec.

## Commits

No Co-Authored-By, no Claude/Anthropic attribution.

## Commands

```
pp2lp check  [--suite=X] [--name=Y] [--job=PFX] [--fresh] [--all-failures]
pp2lp status [--suite=X]
pp2lp gen    [--suite=X] [--alloc=...] [--all]
pp2lp clean  [--lpo] [--cache] [--all] [--suite=X]
pp2lp emit   REPLAY... [-trace]
pp2lp prove  FORMULA [--name NAME]

make help                                       # one-line summary of every target
make build | check | check-all | check-fresh    # default suite is prv
make test NAME=Y [SUITE=X] | test-cache
make gen [ALLOC=N] | prove FORMULA=... | status
make clean | clean-all | repl
```

## Caching

`pp2lp check` skips tests whose `bench/<suite>/.cache/<name>.{ok,fail,skip}`
marker is newer than both the `.replay` and a sentinel (newest of the
`pp2lp` binary + any `lp/**/*.lp`). `--fresh` forces. After LP-rule
signature changes you may need `pp2lp clean --lpo`.

`.ok` body: `"<trust> <admit>"`. `.fail`: raw lambdapi output (NDJSON).
`.skip`: short reason. Cache logic in `ocaml/src/cache.ml`; tests in
`ocaml/test/test_cache.ml`.

## PP limitations (read before writing goals)

- **BOOL membership**: PP can't reason about `a: BOOL` abstractly. Use `btrue`/`bfalse` only as concrete terms in equalities.
- **Cascaded `=>`**: PP's `=>` is left-associative. `(p => q) => (r => s) => g` parses as `((p => q) => (r => s)) => g`. Use `and` for independent hypotheses.
- **Set-theoretic surface**: `eql_set`, pair decomposition, higher-order set operators aren't in the goal formula syntax.
- **Arithmetic**: AR1–AR13 reduce to `B.lp`'s integer primitives. Some emitted proofs carry `trust` for solver-level conjuncts.
- **Trust axioms in prv**: Atelier B corpus exercises documented PP→LP semantic gaps (BOOL membership, arithmetic AC, REPLAY truncation).

## Suites

- **prv** — Atelier B Proof Rules Validator corpus. Not a regression target.
- **og** — frozen pre-baked `.replay`s. Legacy.

## Admits / trust categories

- **`lp/B.lp:16`** — `trust : π P` axiom + B-Book primitives. Intentional.
  No other `admit`s in `lp/`.
- **Emitted `trust`** — emitter passes `trust` at use sites instead of a
  real proof term. See `doc/rules.md` for the full per-rule list; the
  major categories (some tagged by `pp2lp emit -trace`):
  - NRM20–23 subtree close (HOU blocker after λ-applied form) —
    tags `nrm20-shape-trust`, `nrm21-23-trust`, `all7-2nd-child-trust`
  - BOOL31–42 — `V ϵ BOOL` membership (PP can't reason about BOOL abstractly)
  - INS arithmetic-match conjuncts (solver equality bridge)
  - AR2, AR13 — solver-confirmed numeric side conditions

## Replay format

Lines: `[RULE] <goal>` | `[RULE(arg)] <goal>` | `[FIN(result)] <FIN(...)>`.
Rules applied backwards; multi-premise rules branch DFS. `[FIN]` carries
normalisation result. `[STOP_NORM]`, `[NRM]` are phantoms. `[RULE_1]` is
primed (inside ALL7/XST8 result chain); non-`_1` NRM between `_1` and FIN
is bookkeeping.

## References

`doc/spec_pp.md` PP spec · `doc/pp_rules.md` rule summary · `doc/b-book-ref.md` B-Book pointers.
