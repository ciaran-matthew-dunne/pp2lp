# CLAUDE.md

Within the B-Method ecosystem, the Predicate Prover (PP) is an automated theorem
prover for first-order logic and linear arithmetic. Because PP’s source code is
not publicly available, its results are currently trusted without independent 
verification. This project develops `pp2lp`, a tool for reconstructing PP proofs
in LambdaPi, a proof assistant based on the 𝜆Π-calculus modulo rewriting. 

Each of PP's inference rules is encoded as a LambdaPi symbol in `./lp` whose 
type captures the rule's premises and conclusion and whose body proves the rule
sound with respect to a small trusted base built on top of LambdaPi's stdlib. 

PP is instrumented to emit replays of its proofs; pp2lp parses the replay,
rebuilds the proof tree, and emits a tactic script that LambdaPi typechecks.
We prove the soundness of all of PP’s inference rules and reconstruct proofs
across several real-world (`prv`, `apero`) and synthetic (`claude`) benchmarks.

Pipeline: 
`formula -> .but → PP → .trace → REPLAY → .replay → pp2lp → .lp → lambdapi check`.

The main tool is written in OCaml, but is driven by a Python CLI `./pp2lp`.

- `./doc/pp-spec-full.pdf` is the internal documentation for PP,
- `./doc/pp-spec-rules.pdf` is a table specifying the rules used by PP.

- Call `lambdapi` with `--no-colors -v 0 -w --proof-state-on-error`: drops ANSI,
  start/end-checking noise, and critical-pair warnings, and prints goal state on
  an in-proof failure.
- **`pp2lp gen` rewrites a suite**. Run it only when the task *is* corpus 
  generation, never as a debugging reflex.
- **Suites are tests, not a commit gate.** og/prv/claude/apero failures during
  development are expected — don't chase them or hold up a commit on red. 
  Live counts are in `lp/bench/results/<suite>.json` (emit) and
  `<suite>.check.json` (check) after a run, don't store counts in CLAUDE.md.
- Commit messages: plain prose, no Co-Authored-By, no Claude/Anthropic attribution. 
  Don't push unless asked.
- **Off limits unless asked:** `tex/` (the LPAR-26 paper, deadline 21 Jun 2026 AoE).
  Paper-writing guidance lives in `tex/CLAUDE.md` (auto-loads when a session
  touches `tex/`).

## Commands

The pipeline is two decoupled phases: `pp2lp run` parses+translates+writes the
`.lp` (no lambdapi); `pp2lp check` type-checks the emitted `.lp`. Run them in
sequence: `pp2lp run <suite> && pp2lp check <suite>`.

```
pp2lp run                       # emit og → .lp (default suite; parse+translate+write)
pp2lp check                     # type-check og's emitted .lp with lambdapi
pp2lp run claude                # emit a suite; exits non-zero iff a trace fails to emit
pp2lp check claude              # type-check it; exits non-zero iff a .lp fails lambdapi
pp2lp run og/01                 # emit one trace (dossier)
pp2lp check og/01               # type-check one trace, full failure window
pp2lp check apero --filter 'ap_0016'   # subset by name regex → writes <suite>.check.filter.json
pp2lp check apero --filter a,b --exact # exact name set (no substring/regex over-match)
pp2lp check apero --code E_LP_CHECK     # unfold only that code's windows (use with --filter)
pp2lp check og --json           # machine output (also lp/bench/results/og.check.json)
pp2lp check og -q               # summary + by-code histogram (progress heartbeat on stderr)
pp2lp check apero -i            # incremental: skip benchmarks unchanged since they last passed
pp2lp check apero --timeout 30  # override PP2LP_CHECK_TIMEOUT for this run (0 disables)

pp2lp triage apero              # cluster the last run's failures (emit + check) by code+signature (timeouts excluded; --all to include)

pp2lp gen claude                # regen .but/.trace/.replay via krt (PP/REPLAY)
pp2lp gen prv --only replays    # one stage (buts,traces,replays)
pp2lp gen apero --only buts     # apero stage 1: pog2but + select (see Apero)

pp2lp clean                     # drop stale .lpo caches (project lp/ + Stdlib)
```

`--filter`/`--exact`/`--code`/`--timeout` work on both `run` and `check`. `run`
auto-builds the engine (`--no-build` to skip) and writes each `.lp` plus a
`.provmap` next to its `.replay`; the `.lp` write is content-aware (rewritten only
when the emitted text changes, so an unchanged emit keeps its mtime). `check`
reads those back, warming the shared `lp/` objects once up front. Both run suites
in parallel and exit non-zero iff any trace fails. `run` writes
`lp/bench/results/<suite>.json`, `check` writes `<suite>.check.json`; a `--filter`
run writes the `.filter.json` variant, so neither clobbers the baseline. A
benchmark with no `.lp` (emit failed, or `run` not run) is reported by `check` as
`no_lp` (code `E_NO_LP`).

`check -i` (incremental) skips a benchmark whose `.lpo` is newer than its `.lp`
and the shared library objects — i.e. it passed last time and nothing it depends
on changed (lambdapi only writes a `.lpo` on success, so a prior failure always
re-runs). It trusts mtimes, not lambdapi, so after a lambdapi upgrade run `pp2lp
clean` (or a plain `check`) once before using `-i` again. The default `check`
always really checks.

Child-process caps (env, 0 disables): 
  `PP2LP_CHECK_TIMEOUT`, `PP2LP_EMIT_TIMEOUT`, `PP2LP_GEN_TIMEOUT` 
   (all 10 s; the slowest prv trace needs ~7.4 s, so don't lower them), 
   `PP2LP_CHECK_MEM_GB` (4 GiB). 
`run`/`check --timeout SECS` overrides the emit/check cap for one run (0 disables).
A timeout reports its own code (`E_LP_TIMEOUT`/`E_TIMEOUT`), distinct from a real failure.

## Checks (fastest first — climb only as far as the change needs)

| check                                         | time    | catches                                   |
|-----------------------------------------------|---------|-------------------------------------------|
| `cd ocaml && dune build`                      | seconds | type/exhaustiveness errors (warn 8 fatal) |
| `cd ocaml && dune runtest`                    | seconds | emitter output drift (replay→.lp)  |
| `python3 lp/bench/test_cli.py`                | seconds | the OCaml↔Python error-code contract      |
| `./pp2lp run og -q`                           | <1 s    | emit smoke (30 traces → .lp)              |
| `./pp2lp check og -q`                         | ~3 s    | type-check smoke (30 traces)              |
| `./pp2lp run <s> -q && ./pp2lp check <s> -q`  | ~5 min  | full regression (s = prv, then claude)    |

Pre-commit minimum: `cd ocaml && dune runtest && ./pp2lp run og -q && ./pp2lp
check og -q`. Add prv + claude when `ocaml/` or non-bench `lp/` changed. Rough
baseline: og 30/30, prv
70/70, claude most of ~2300 (every goal is a genuine theorem PP proves bare; the
suite was scaled to surface failures, so the ✗ are the emit/translate frontier:
FIN_INS, INS, Farkas/AR, ALL5_1). Live numbers in `lp/bench/results/`.

## Source layout

```
pp2lp                  the single CLI (Python): run, check, triage, gen, clean.
ocaml/src/             the engine (each core module has a .mli):
  parse_replay.ml        .replay → rule lines
  rule_db.ml             rule metadata + the typed emit-dispatch key
  proof_tree.ml          rule lines → tree (replay state machine)
  translate.ml           tree → lp_tree walker (main proof vs Res-chain)
  rule_emit.ml           per-rule refine construction (exhaustive match)
  emit_ctx.ml            mutable ctx + hyp/witness/INS searches
  arith_proofs.ml        generated arithmetic proofs (sum / cancellation / Farkas)
  syntax_pp.ml           PP AST + flatten_binds + the shared exp traversal
  errors.ml              E_*-coded failwith helper (CLI classifies by prefix)
  + pp_lp, emit_pp, lp_tree, emit_lp, free_vars, lexer.mll, parser.mly, reconstruct, bin/main.ml
ocaml/test/            tests: replay→.lp vs committed (dune runtest; dune promote)
lp/
  B.lp                   trusted base: constants, axioms, reduction rules
  lemmas/*.lp            proved lemmas (Int arith laws, Tuple η/cong, ConjList surgery)
  Prelude.lp             re-exports B + lemmas/* + rules/* — the emitter's sole import
  rules/*.lp             per-section rule lemmas (All, Arith, Axm, Bool, …)
  bench/<suite>/<name>/  per-benchmark artifacts (apero nests <suite>/<proj>/<name>/)
  bench/test_cli.py      CLI self-tests + repo contract checks
  bench/results/         per-run JSON: <suite>.json (emit) + <suite>.check.json (check) (gitignored)
vendor/atelierb/       vendored REPLAY.kin (used by gen)
vendor/apero/pog/      the CLEARSY POG dataset (gitignored)
```

## Suites

| suite      | what | source of truth | tracked |
|------------|------|-----------------|---------|
| **og**     | original 30 traces | its `.trace`/`.replay` (no `.but`) | `.trace` + `.replay` |
| **prv**    | proof-rule-validation suite | checked-in `.but` | `.but` |
| **claude** | synthetic goals generated by claude | `lp/bench/claude/goals.txt` | `.but` |
| **apero**  | CLEARSY industrial POs (current work) | `./vendor/apero/pog` (Zenodo 10.5281/zenodo.7050797) | nothing (regenerable) |

## LP gotchas

- Don't match on integer literals in LambdaPi rewrite rules patterns. Use their 'normal forms'.
- `sequential` rule blocks are order-sensitive.
- Stale `.lpo` after a lambdapi upgrade or lp/ edit storm → `pp2lp clean`.

## Errors

| code | meaning | start at |
|------|---------|----------|
| `E_UNKNOWN_RULE` | rule not in the database | add it to `rule_db.ml` (arity/phantom/flags) |
| `E_DISPATCH` | unsupported rule shape / dispatch arm | `translate.ml` / `rule_emit.ml` |
| `E_TREE_BUILD` | replay → tree reconstruction failed | `proof_tree.ml` (`PP2LP_DEBUG_REPLAY=1`) |
| `E_PARSE` | bad replay line | `parse_replay.ml` (inspect the reported column) |
| `E_INS` | INS contradiction search failed | `emit_ctx.ml` (message dumps hyps + witnesses) |
| `E_EMIT` | other emit-side failure | the message names the rule/variable |
| `E_LP_CHECK` | lambdapi rejected the emitted `.lp` | the window's goal state |
| `E_REPLAY_TRUNCATED` | REPLAY dropped the continuation | upstream; dropped at gen |
