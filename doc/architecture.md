# Architecture notes

## Current shape (post-consolidation)

```
Makefile (88 lines)             ← thin shim: every target forwards to pp2lp ...
   │
   ├── pp2lp (OCaml binary, ocaml/_build/default/bin/main.exe)
   │     subcommands:
   │       emit | parse | prove | synth          (replay → .lp / formula → .lp)
   │       gen                                   (shells out to gen_traces.py)
   │       check | status | coverage | clean    (suite orchestration)
   │       debug | show-fail | diff             (per-test debugging)
   │       lp-check | lp-axioms | lp-debug      (file-level lambdapi tooling)
   │     library modules of interest:
   │       suite.ml      — per-suite metadata table
   │       cache.ml      — typed cache markers + sentinel logic
   │       runner.ml     — emit + lambdapi check + cache writeback
   │       coverage.ml   — replaces rule_coverage.sh
   │       lp_diag.ml    — NDJSON parser + pretty-printer (replaces format_error.py)
   │       lp_tools.ml   — file-level lambdapi scanning (assumptions / rules)
   │       json_out.ml   — minimal JSON writer + parser (no yojson dep)
   │
   ├── bench/gen_traces.py (355 lines, Python)
   │     wraps `kr3` (Atelier B prover); pp2lp gen invokes it.
   │     Kept in Python — Python is the right tool for wrapping a flaky
   │     external binary with diverse failure modes.
   │
   └── lambdapi (separate binary, opam-installed)
         used directly + via lambdapi-mcp (separate repo).
         pp2lp check shells out to `lambdapi check [--json] -c FILE`.
```

Per-test cache lives in `bench/<suite>/.cache/<name>.{ok,fail,skip}`.
Markers are mtime-compared against a sentinel (max of pp2lp binary
mtime and newest `lp/**/*.lp` mtime). The on-disk format is unchanged
from the previous Make-managed cache — pre-existing markers remain
valid through this migration.

## What moved, what stayed, what dropped

### Moved into OCaml
- `Makefile`'s `RUN_CHECK` macro (~100 lines of inline shell): now
  `Cache.lookup` + `Runner.run_one`. Behaviour parity tested in
  `ocaml/test/test_cache.ml` (28 cases).
- `Makefile`'s `status` rule: now `pp2lp status`, reads markers via
  `Cache.list_markers`.
- `Makefile`'s per-suite ALLOC table and SYNTH_SUITES set: now
  `Suite.all` in `ocaml/src/suite.ml`.
- `Makefile`'s lambdapi --json detection: now `Runner.detect_lambdapi_json`.
- `bench/format_error.py`: deleted; replaced by `Lp_diag.format_for_terminal`
  and `Lp_diag.parse_ndjson`.
- `bench/rule_coverage.sh`: deleted; replaced by `pp2lp coverage` /
  `Coverage.print_by_suite`.

### Stayed in place
- `bench/gen_traces.py` — `pp2lp gen` shells out to it.
- `dune` build system for OCaml.
- The Lambdapi backend (`lp/`).

## pp2lp / lambdapi-mcp split (lambdapi tooling)

| Tool                                | Lives in    | Why |
| ----------------------------------- | ----------- | --- |
| lp-check / lambdapi_check           | pp2lp + MCP | pp2lp = file-batch + JSON for CI; MCP = single-file LSP probe |
| lp-axioms / lambdapi_axioms         | pp2lp       | Pure file scan + require resolution; no LSP value |
| lp-probe (compute/type/print/goals/proofterm) | pp2lp | Insert lambdapi command in sibling probe file → bounded, line-precise output |
| lp-debug                            | pp2lp       | Insert `debug +/-FLAGS;` toggles → lambdapi only emits trace for bracketed region |
| try / symbols                       | MCP only    | Interactive (try) or LSP-elaborated state (symbols) |

The reshape: most of what looked like LSP-only territory turns out to
be expressible as "insert a lambdapi command at line N and read the
output". `pp2lp lp-probe` covers `compute`, `type`, `print SYMBOL`
(toplevel) and `print;`, `proofterm;` (in-proof) — i.e., everything
the MCP `query`/`goals`/`proofterm` tools surface. `lp-debug` uses
`debug +FLAGS; … debug -FLAGS;` so lambdapi only logs trace inside
the bracket — no slicing required, output bounded by construction.

Stream split: command echoes go to stdout; debug traces to stderr.
`lp-probe` reads stdout (for the command's result); `lp-debug` reads
stderr (for the bracketed trace).

Probe-file mechanics: copy the original to
`<dir>/_pp2lp_probe_<stem>_<pid>.lp` (same dir → `require` resolution
unchanged), insert the command(s), run `lambdapi check`, unconditional
cleanup via `Fun.protect`.

### New surfaces
- `pp2lp emit --json` — NDJSON one record per file:
  `{ok, kind, file, lp, trust_count, admit_count, traces[]}`.
  `traces` carries the `[emit]` dispatch decisions previously written
  to stderr only.
- `pp2lp check --json` — NDJSON one record per test plus a final
  summary record. Designed for the lambdapi-mcp consumer.
- `pp2lp debug REPLAY` — prints the PP rule sequence and the in-memory
  emitter dispatch trace for one replay.
- `pp2lp show-fail SUITE NAME` — pretty-prints the `.fail` marker and,
  when the lambdapi error has a location, shows ±3 lines from the
  emitted `.lp`.
- `pp2lp diff REPLAY` — side-by-side PP rule sequence and emitted LP.
  Useful when investigating why the emitter handled a step "oddly".
- `pp2lp lp-check FILE...` — type-check one or more `.lp` files without
  going through the LSP. NDJSON with `--json`.
- `pp2lp lp-axioms FILE... [--scope=file|project]` — file-scope
  scanner for unproved assumptions, defined-by-rules symbols, and
  `admit` tactics. Project scope follows `require` within the project
  (no Stdlib walk — the lambdapi-mcp is the right tool for that).
- `pp2lp lp-debug FILE --flags=FLAGS` — `lambdapi check --debug=FLAGS`
  with `--pattern` / `--head` / `--tail` / `--save-to` filters; deletes
  the `.lpo` first to force re-elaboration.

### Dropped
- The legacy ANSI-stripping fallback in `format_error.py` for
  pre-`--json` lambdapi builds is preserved in `Lp_diag.format_for_terminal`
  (it's still useful when the buffer contains both NDJSON records and
  raw lambdapi text).
- Inline shell loops in the Makefile.
- Per-rule mtime tracking in Make. (Make's parallelism was largely
  wasted on a sequential workload.)

## Caching, in one paragraph

`Cache.lookup` returns `Some kind` iff a marker exists, is newer than
the `.replay`, and has mtime ≥ sentinel; otherwise `None`. Precedence
when multiple are fresh: `.ok` > `.skip` > `.fail`. `Runner.run_one`
calls lookup first, runs emit + lambdapi check on miss, and writes the
appropriate marker. The full shell-loop semantics from the old `RUN_CHECK`
macro are pinned in `test_cache.ml`.

## Why JSON

`lambdapi check --json` exists; consumers downstream of `pp2lp` (the
MCP server, future tooling) want structured, not text. Adding `--json`
to `pp2lp emit` first let `pp2lp check` use the structured payload
internally instead of grep'ing the .lp output for `trust` / `admit` —
and the same path is what external consumers get.

## Layout

```
ocaml/src/
  json_out.ml     — minimal JSON I/O
  suite.ml        — suite metadata
  lp_diag.ml      — lambdapi NDJSON diagnostics
  cache.ml        — per-test cache markers + sentinel
  coverage.ml     — per-rule × per-suite coverage
  runner.ml       — emit + lambdapi check + cache writeback
  ... existing emitter, parser, etc.
ocaml/bin/main.ml — CLI dispatch
ocaml/test/
  test_cache.ml   — unit tests for the cache logic
```
