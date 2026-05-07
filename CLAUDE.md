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
make help
make build
make gen-traces DIR=bench/prv [OUT_DIR=bench/prv]
make gen-replays DIR=bench/prv [OUT_DIR=bench/prv]   # optional debugging only
make check [NAME=01] [SUITE=og]
make check TRACE=bench/og/01.trace
make clean | repl
```

## Trace Pipeline

The OCaml tool reads PP `.trace` files directly. It does not read REPLAY
output and has no cache layer. `bench/gen_traces.py` runs PP and writes
`.trace`; `bench/gen_replays.py` is separate and only creates optional
`.replay` files for debugging.

## PP limitations (read before writing goals)

- **BOOL membership**: PP can't reason about `a: BOOL` abstractly. Use `btrue`/`bfalse` only as concrete terms in equalities.
- **Cascaded `=>`**: PP's `=>` is left-associative. `(p => q) => (r => s) => g` parses as `((p => q) => (r => s)) => g`. Use `and` for independent hypotheses.
- **Set-theoretic surface**: `eql_set`, pair decomposition, higher-order set operators aren't in the goal formula syntax.
- **Arithmetic**: AR1–AR13 reduce to `B.lp`'s integer primitives. Some emitted proofs carry `trust` for solver-level conjuncts.
- **Trust axioms in prv**: Atelier B corpus exercises documented PP→LP semantic gaps (BOOL membership, arithmetic AC).

## Suites

- **prv** — Atelier B Proof Rules Validator corpus. Generated traces are ignored by git.
- **og** — small checked-in trace corpus for smoke tests.

## Admits / trust categories

- **`lp/B.lp:16`** — `trust : π P` axiom + B-Book primitives. Intentional.
  No other `admit`s in `lp/`.
- **Emitted `trust`** — emitter passes `trust` at use sites instead of a
  real proof term for inline side-condition arguments. It must not emit
  whole-goal `refine trust`. See `doc/rules.md` for the full per-rule list;
  the major categories:
  - BOOL31–42 — `V ϵ BOOL` membership (PP can't reason about BOOL abstractly)
  - INS arithmetic-match conjuncts (solver equality bridge)
  - AR2–AR9, AR13 — solver-confirmed numeric/equality side conditions
- **Unsupported shapes** — the trace-first emitter should fail explicitly
  rather than closing a whole goal with `trust`.

## Trace Format

Lines are `[RULE] &`, `[RULE(arg)] &`, `[FIN(result)] &`, `[STOP_NORM] &`,
`[NRM] &`, followed by the final parenthesized goal. PP writes rules in
right-first DFS postorder; `ocaml/src/proof_tree.ml` rebuilds the tree with
a stack.

## References

`doc/spec_pp.md` PP spec · `doc/rules.md` rule notes · `doc/b-book-ref.md` B-Book pointers.
