# Feature request: `--json` output mode for the Lambdapi CLI

## Problem

Projects that batch-invoke `lambdapi` (compilers, CI harnesses, IDE integrations,
benchmark drivers) currently have to scrape human-oriented stderr/stdout to learn
*what happened*. The current output is:

- a mix of ANSI-coloured status lines ("Start checking …", "End checking …"),
- errors written to stderr with file:line:col banners,
- warnings interleaved with info,
- summaries printed only at the very end.

This is fragile. Colour codes leak through; message wording changes between
releases; multi-line errors are awkward to reassemble; we cannot tell whether a
given goal was closed by `admit`, `trust`, or a real proof without grepping.

In **pp2lp** specifically, our Makefile harness parses `lambdapi check` output
for every one of ~600 generated `.lp` files per run, and keeps a per-file cache
of `{ok, fail, skip}` plus a trust count. We currently implement this with
regexes over the coloured text, which is both slow and brittle — a wording tweak
in Lambdapi has already broken us once.

## Proposal

Add a `--json` flag to the top-level `lambdapi` binary (applying at least to
`check`, and ideally to `decision`, `lsp`, and any other long-running
subcommand). When set:

- **All diagnostic output goes to stdout as newline-delimited JSON** (one
  complete JSON object per line — the JSON Lines / `ndjson` convention).
- **Nothing human-oriented is printed** — no ANSI, no "Start checking …"
  banners. Only JSON records on stdout; stderr reserved for hard crashes /
  panics.
- **Exit code semantics unchanged**: 0 on success, non-zero on any
  error-severity record.

## Record schema (draft)

Every record has at least:

```json
{ "kind": "<record-kind>", "ts": "2026-04-22T12:34:56.789Z" }
```

Proposed record kinds:

### `file_start` / `file_end`

```json
{"kind": "file_start", "file": "bench/foo.lp"}
{"kind": "file_end",   "file": "bench/foo.lp", "elapsed_ms": 412, "status": "ok"}
```

`status` is `"ok"` | `"error"` | `"aborted"`.

### `diagnostic`

```json
{
  "kind": "diagnostic",
  "severity": "error" | "warning" | "info",
  "file": "bench/foo.lp",
  "range": { "start": {"line": 42, "col": 7}, "end": {"line": 42, "col": 19} },
  "code": "type-mismatch",         // stable, machine-readable; optional
  "message": "Type mismatch: ...", // human-readable
  "related": [                     // optional, for "expected X, got Y" style
    { "label": "expected", "range": {...}, "message": "..." },
    { "label": "got",      "range": {...}, "message": "..." }
  ]
}
```

The critical bit is **`code`**: a short, stable identifier per diagnostic class
(e.g. `type-mismatch`, `unknown-symbol`, `rewrite-nontermination`,
`lpo-incompatible`, `parse-error`). Tools can branch on `code` without regex
work, and the wording of `message` can evolve freely.

### `proof_obligation`

For each proof tactic script that closes (or fails to close) a goal:

```json
{
  "kind": "proof_obligation",
  "file": "bench/foo.lp",
  "symbol": "my_lemma",
  "status": "proved" | "admitted" | "trust" | "failed",
  "elapsed_ms": 23
}
```

This single field would let pp2lp replace its regex-based trust counter
(`3238 trust` in the current prv run) with a one-pass aggregate.

### `summary`

Emitted once at the end of a `check` invocation:

```json
{
  "kind": "summary",
  "files_checked": 100,
  "files_ok": 53,
  "files_failed": 17,
  "obligations_proved": 842,
  "obligations_admitted": 0,
  "obligations_trust": 3238,
  "elapsed_ms": 48912
}
```

## Stability guarantees we'd like

- The **set of `kind` values** and the **set of `code` values** are part of a
  documented, versioned schema — adding new values is a minor-version bump,
  removing or renaming is a major-version bump.
- Field additions within a record are always backwards-compatible (consumers
  must ignore unknown fields).
- `--json-schema-version` flag prints the schema version for negotiation.

## Why JSON Lines, not a single JSON blob

- Streams naturally — pp2lp can update its progress bar per file without
  waiting for the whole run.
- Survives `SIGINT` / crashes — partial logs remain parseable up to the last
  complete line.
- Trivial to `tail`, `grep -c kind`, or pipe through `jq` interactively.

## Non-goals

- We are *not* asking for the LSP protocol to be repurposed for CLI use —
  LSP is request/response and stateful; this is one-shot batch output.
- We are *not* asking for JSON *input* (source files stay in `.lp`).

## Minimum viable version

If the full schema is too much for a first pass, the single biggest win for
pp2lp would be:

1. `file_end` records with `status` and `elapsed_ms`,
2. `diagnostic` records with `severity`, `file`, `range`, and `code`,
3. a `summary` record at the end.

`proof_obligation` and everything else can follow later.

## Requesting party

pp2lp (Predicate Prover → Lambdapi translator). We batch-invoke `lambdapi
check` over ~600 generated files per CI run; structured output would let us
drop ~80 lines of regex-based output parsing and stop breaking on cosmetic
Lambdapi output changes.
