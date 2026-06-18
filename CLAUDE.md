# CLAUDE.md

Maintainer notes for **pp2lp** — it translates Atelier B Predicate Prover (PP)
proof replays to Lambdapi and type-checks them independently.

Round trip: `formula → PP → .trace → REPLAY → .replay → pp2lp → .lp → lambdapi check`.

**`./pp2lp`** at the repo root does everything: builds the OCaml engine, emits
Lambdapi, type-checks it, and reports. The binary under `ocaml/_build/` is
internal — you drive `./pp2lp`. 

## Ground rules

- When calling `lambdapi`, use the `--no-colors` flag to avoid ANSI codes,
  and `-v 0` to avoid the 'Start checking ...' and 'End checking ...' bloat,
  and `--proof-state-on-error` flag to get better info about in-proof failures,
  and `-w` to disable warnings about critical pairs, pattern variables, etc.
- **`pp2lp gen` rewrites a suite**, wiping every benchmark dir not in its source
  of truth (goals.txt / checked-in `.but`s), tracked orphans included. Run it only
  when the task *is* corpus generation, never as a debugging reflex.
- **Suites are tests, not a commit gate.** og/prv/claude/apero failures during
  development are expected — don't chase them or hold up a commit on red. 
  Live counts are in `lp/bench/results/<suite>.json` after a run.
- Commit messages: plain prose, no Co-Authored-By, no Claude/Anthropic attribution. 
  Don't push unless asked.
- **Off limits unless asked:** `tex/` (the LPAR-26 paper, deadline 21 Jun 2026 AoE),
  `notes.md`, `admin/`, `doc/`, `vendor/`.

## Commands

```
pp2lp run                       # check og (default)
pp2lp run claude                # check a suite; exits non-zero if any trace fails
pp2lp run og/01                 # one trace, full failure window
pp2lp run apero --filter 'ap_0016'   # subset of a suite by name regex
pp2lp run apero --code E_TREE_BUILD  # unfold only that code's windows (use with --filter)
pp2lp run og --json             # machine output (also lp/bench/results/og.json)
pp2lp run og -q                 # summary + by-code histogram only

pp2lp gen claude                # regen .but/.trace/.replay via krt (PP/REPLAY)
pp2lp gen prv --only replays    # one stage (buts,traces,replays)
pp2lp gen apero --only buts     # apero stage 1: pog2but + select (see Apero)

pp2lp clean                     # drop stale .lpo caches (project lp/ + Stdlib)

pp2lp test                      # type-check the rule-base unit tests (lp/tests/)
pp2lp test --filter Nrm         # one test module; -q for summary only
```

`run` auto-builds the engine (`--no-build` to skip), runs suites in parallel
(shared `lp/` objects compile once up front), and exits non-zero iff any trace
fails. Child-process caps (env, 0 disables): `PP2LP_CHECK_TIMEOUT`,
`PP2LP_EMIT_TIMEOUT`, `PP2LP_GEN_TIMEOUT` (all 10 s; the slowest prv trace needs
~7.4 s, so don't lower them), `PP2LP_CHECK_MEM_GB` (4 GiB). A timeout reports its
own code (`E_LP_TIMEOUT`/`E_TIMEOUT`), distinct from a real failure.

## Checks (fastest first — climb only as far as the change needs)

| check                                         | time    | catches                                   |
|-----------------------------------------------|---------|-------------------------------------------|
| `cd ocaml && dune build`                      | seconds | type/exhaustiveness errors (warn 8 fatal) |
| `cd ocaml && dune runtest`                    | seconds | emitter output drift (replay→.lp)  |
| `python3 lp/bench/test_cli.py`                | seconds | the OCaml↔Python error-code contract      |
| `./pp2lp test`                                | <1 s    | rule signatures drifting from their spec  |
| `./pp2lp run og -q`                           | ~3 s    | end-to-end smoke (30 traces)              |
| `./pp2lp run prv -q && ./pp2lp run claude -q` | ~5 min  | full regression                           |

Pre-commit minimum: `cd ocaml && dune runtest && ./pp2lp run og -q`. Add prv +
claude when `ocaml/` or non-bench `lp/` changed. Rough baseline: og 30, prv ~70,
claude ~1020 of 1129 (every goal is a genuine theorem PP proves bare — see the
goals.txt header; the ~110 ✗ are the emit/translate frontier those real proofs
exercise: FIN_INS, INS search, Farkas/AR). Live numbers are in `lp/bench/results/`.

## Source layout

```
pp2lp                  the single CLI (Python): run, gen, clean.
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
  B.lp                   trusted base: constants, axioms, defs + reduction rules
                         (membership, pairs, BOOL, Tuple n, integers, ⋀/Res)
  lemmas/*.lp            proved lemmas: Int (arith laws), Tuple (η, !!/?? cong,
                         ♢/♡ bridges), ConjList (⋀ surgery, conj_concat_eq)
  Prelude.lp             re-exports B + lemmas/* + rules/* — the emitter's sole import
  rules/*.lp             per-section rule lemmas (All, Arith, Axm, Bool, …)
  tests/*.lp             rule-base unit tests (one file per rules/ module; `pp2lp test`)
  bench/<suite>/<name>/  per-benchmark inputs/artifacts (see Suites)
  bench/test_cli.py      CLI self-tests + repo contract checks
  bench/results/         per-run JSON (gitignored)
vendor/atelierb/       vendored REPLAY.kin (used by gen)
vendor/apero/pog/      the CLEARSY POG dataset (gitignored)
```

## Suites

| suite      | what | source of truth | tracked |
|------------|------|-----------------|---------|
| **og**     | original 30 traces | its `.trace`/`.replay` (no `.but`) | `.trace` + `.replay` |
| **prv**    | proof-rule-validation suite | checked-in `.but` | `.but` |
| **claude** | synthetic goals generated by claude | `lp/bench/claude/goals.txt` | `.but` |
| **apero**  | CLEARSY industrial POs (current work) | (Zenodo
10.5281/zenodo.7050797) `./vendor/apero/pog` | nothing (regenerable) |

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

## Apero (the current work)

Industrial proof obligations from CLEARSY's open POG corpus . No Atelier B path goes `.pog → PP`, so apero converts
each obligation to a `.but` (`gen_apero_buts`: pog2but + dedup + the
`PP2LP_APERO_MAX_PREMISE` cap, default 50), then runs the usual PP → REPLAY →
emit → check.

### Known gaps (not regressions; full detail in INTERNALS.md)
- **REPLAY truncation** — sometimes the replay tool drops subproofs; usually on `ALL7`/`XST8`/`OR3_1`/`XST8_1`/`ALL7_1`. often we can confirm this by comparing the `.replay` and the `.trace` file. such cases should be removed from our benchmark suite. 
- **`FIN_INS` / `__INSTANCIATION` replay lines** — novel INS-evidence markers that we only find in the `apero` suite. unsure how they differ from `INS`.
