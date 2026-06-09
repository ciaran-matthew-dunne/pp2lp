# CLAUDE.md

Maintainer notes for **pp2lp** — translates Atelier B Predicate Prover
(PP) proof replays to Lambdapi for independent type-checking.

Round trip: `formula → PP → .trace → REPLAY → .replay → pp2lp → .lp → lambdapi check`.

One command does everything: **`pp2lp run`** (the executable `./pp2lp` at the
repo root). It builds the OCaml engine, emits Lambdapi, type-checks it, and
reports — for a whole suite (exit non-zero if any benchmark fails) or one trace
(a detailed per-trace report). The OCaml binary under `ocaml/_build/` is an
internal engine; you drive `./pp2lp`.

The generated `.lp` has no comments. The engine instead writes a table mapping
each `.lp` line to the PP rule, replay line, and goal that produced it. On a
lambdapi error, `pp2lp` looks the line up and shows three things side by side:
the `.lp` at the error, the `.replay` step it came from, and the matching
`lp/rules/` lemma.

## Commands

```
pp2lp run                       # check the og suite
pp2lp run synth                 # check a suite (any ✗ ⇒ exit 1)
pp2lp run og/01                 # check one trace; a failure shows snippet panels
pp2lp run synth/x --lp-debug=u  # also probe lambdapi (debug +u) → a .lp.debug panel
pp2lp run og --json             # machine output (also bench/results/og.json)
pp2lp run og -q                 # summary only (suppress failure windows)

pp2lp gen synth                 # (re)gen .but/.trace/.replay via krt (PP/REPLAY)
pp2lp gen prv --only replays    # one stage only (buts,traces,replays)
```

`run` auto-builds the engine first (`--no-build` to skip). Suites run in
parallel (shared `lp/` objects are compiled once up front, so a cold run doesn't
race); per-trace outcome is `✓` / `⚠` / `✗`, exit status non-zero iff any trace
fails. Suites: `og` (default), `prv`, `prv-no-arith`, `synth`, `nrm_test`,
`gemini`.

Child-process caps (env-tunable, 0 disables): `PP2LP_CHECK_TIMEOUT` (60s),
`PP2LP_EMIT_TIMEOUT` (30s), `PP2LP_CHECK_MEM_GB` (4 GiB `RLIMIT_AS`). They keep a
runaway goal (e.g. `x: NAT` membership) from taking down the host — it fails
fast rather than hanging.

`pp2lp run` shells out to the engine (`ocaml/_build/default/bin/main.exe emit`)
and `lambdapi`; `pp2lp gen` shells out to Atelier B's `krt` +
`vendor/atelierb/<plat>/REPLAY.kin`. You never call them directly.

## Mental model

PP is Atelier B's automated first-order prover. A `.but` file (formula + flags)
becomes a `.trace` (postorder), then REPLAY turns that into a `.replay`: sequent
proof nodes prefix-style (rule before child subproofs), and the result-chain
child of a branching quantifier (ALL7 / XST8) emitted *before* the branch rule.
Each line carries the per-rule formula annotation PP saw.

`pp2lp` parses the replay, rebuilds the tree (`proof_tree.ml`), and emits an
`opaque symbol` whose body is a tactic script — each PP rule becomes a
`refine RULE …` against a lemma in `lp/rules/`. Lambdapi type-checks the symbol.

Three rule shapes, decoded by `Rule_db.strip_suffix` / `is_primed`:

- **base** — `[AND2]`. Plain LP refine.
- **`_1` primed** — `[AND2_1]`. Inside a Res-typed equality chain preceding a
  branching quantifier.

Branching rules (`ALL7`, `XST8`) are two-child: a Res-typed chain plus a
continuation under the bound variable.

## Source layout

The OCaml pipeline (`ocaml/src/`, core modules carry `.mli`):
`parse_replay.ml` (.replay → rules) → `rule_db.ml` (rule metadata + the typed
`emit` dispatch key) → `proof_tree.ml` (rules → tree) → `translate.ml` (tree →
lp_tree walker: sequence/assume/branch, main + Res-chain, 
`prov_of`) → `rule_emit.ml` (per-rule `refine`, exhaustive emit match) →
`pp_lp.ml` (PP AST → LP source). Supporting: `lexer.mll`/`parser.mly`,
`syntax_pp.ml`/`emit_pp.ml` (PP AST), `free_vars.ml`, `emit_ctx.ml`
(hyp/witness/INS searches), `lp_tree.ml`, `emit_lp.ml` (symbol + header),
`reconstruct.ml` (top-level glue). CLI entry: `ocaml/bin/main.ml emit`.

```
lp/
  lambdapi.pkg       package_name = pp2lp
  B.lp               B-Book primitives + the intentional `trust` axiom (line 17)
  ConjList.lp        n-ary conjunction (⋀) abstraction layer
  Rules.lp / Quant.lp   require-open aggregator; quantifier helpers (!! ?? ♢ ♡)
  rules/*.lp         per-section rule lemmas (All, Arith, Axm, Bool, Conj, Disj,
                     Eq, Equiv, Impl, Neg, Nrm, Res, TrueFalse, Xst)
  bench/<suite>/<name>/   per-benchmark: <name>.{but,trace,replay,lp,lpo}
                     (.lp/.lpo/.lp.* gitignored; og's .trace/.replay tracked)

pp2lp                the single CLI (Python): emit, check, gen, audit, debug.
bench/               test_cli.py (CLI self-tests) + results/ (JSON, gitignored)
vendor/atelierb/<plat>/REPLAY.kin   vendored Atelier B REPLAY tool (used by gen)
doc/                 pp-spec-full.pdf (PP spec, ch. 1–10) +
                     pp-spec-rules.pdf (rule-recap annex). Both gitignored.
```

## Workflows

### Debugging a failing trace

Suite results **stream live** in completion order. On a TTY, passes only advance
a single in-place `done/total` counter (no scrollback flood at suite scale) and
failures unfold their full **failure window**; redirected/piped, each pass is one
compact `✓ name` line. `-q` suppresses the stream (summary line only, clean gate).

The failure window is one numbered snippet per related file, each headed by
`filename:position` with the relevant line marked `>`:
- the **`<name>.probe.lp`** at the error — a persisted, re-checkable copy of the
  emitted `.lp` with `print;` spliced into the failing tactic — followed by a
  prettified **`goal state`** panel (the hypotheses + `⊢ goal` lambdapi was on);
- the `.replay` step that produced it;
- the failing rule's `lp/rules/*.lp` signature.

`--lp-debug=CODE` additionally turns on `debug +CODE` in that same probe run and
surfaces the cleaned, prettified `[tag]` trace (`u`=unification, `r`=rewrite,
`t`=tactics, `w`=whnf; bare ⇒ `u`). Avoid `i` — type inference crashes
lambdapi's printer on our HO goals. The probe is the only artifact written
(`<name>.probe.lp`, gitignored); re-check it directly to reproduce the state.

An emit-side `Failure` → `translate.ml` / `proof_tree.ml` / `parse_replay.ml`;
the report prints a stable error code (`E_UNKNOWN_RULE`, `E_ARITY`, `E_DISPATCH`,
`E_TREE_BUILD`, `E_PARSE`, …) and a hint. Replay→tree state machine:
`PP2LP_DEBUG_REPLAY=1`.

### Inspecting LP goals / debugging LP rules

Use the **sibling-probe** convention — a `lp/rules/Foo_probe.lp` that
`require open`s the module and `print`s/`compute`s the lemma, then `lambdapi
check` it. To inspect a proof's mid-state, copy the emitted `NAME.lp` and insert
`print; proofterm;` before a tactic — or use `--lp-debug=u`. **Delete probe
files when done.** Clear stale artifacts with `git clean -Xf lp/bench bench/results`.

### Adding a corpus trace

1. Drop `lp/bench/SUITE/name/name.but` (or add a line to a suite's `goals.txt`).
2. `pp2lp gen SUITE` — runs PP/REPLAY (krt); a truncated replay is dropped here,
   with a warning.
3. `pp2lp run SUITE/name` — emit + type-check.

### Pre-commit audit

1. `pp2lp run og` must pass (30 ✓, exit 0).
2. `rg -n '\badmit\b' lp/ | rg -v 'B.lp:17'` — must print nothing. Only the
   `trust` axiom at `lp/B.lp:17` may be an admit.
3. `rg 'refine trust;\s*$' lp/bench/og/` — no whole-goal `trust` in emitted og.
   Inline `trust` as a refine *argument* is fine; a bare `refine trust;` means
   the emitter gave up.
4. No stray probe files (`*_probe.lp`, `*_test.lp`, `*_dbg.lp`) under `lp/`.

All suites except `claude` are clean gates (`claude` keeps one known ✗ —
see Known broken).

## Known broken

`og` (30), `prv` (70), `synth` (107), `nrm_test` (42), and `gemini` (422) are
green. `claude` is 222/223 — it probes the frontier on purpose. Residuals:

- **`[ARITH] <FAUX>` solver terminal** (`claude/nar_leq_zero`, the one ✗).
  PP's linear solver closes a leaf (⊥ from the assumed `… ≤ 𝟎` hyps) without
  recording a certificate; `rule_db` raises `E_UNKNOWN_RULE`. Needs a small
  Farkas-style combination search over the ≤-hyps emitting a generated
  add-mono proof (same no-trust approach as the reorder bridges).
- **Chain AR7_1/AR8_1.** Not exercised by any current suite (the gemini goals
  were dropped); would still fail at tree-build — the result-chain has no
  STOP_1 leaf seed and an AR9_1/AR7_1 same-formula pair the one-node-per-line
  postfix model can't place. Replay-format work in `proof_tree.ml`.

Fixed 2026-06-09 (see git log): unary numeral OOM (big literals now emit as
decimal, parsed via Stdlib.Nat's builtins + B.lp's `int_lit` coercion — never
force whnf of a big `int_lit`); EQS2 reshaped to the spec's `FAUX ⇒ R` premise
with emitter-supplied `eql_set` store evidence; ECTR1–6 argument synthesis;
mid-list `⊤` erasure (`mk_0` discharged leaves + `concat` ⊤-rules); explicit
`Res`-term branching emission (chains passed as `refine ALL7 (λ v, …) _`);
ALL3R for chain-side nested-binder merges; explicit `@AXM9_1`/`IMP5_1`
arguments.

PP emits a few identifiers with a leading `_` (`_eql_set`, `_pj1`, `_pj2`); the
lexer treats `_` as a valid identifier-start and the emitter maps them to their
LP names (`eql_set`, `pj1`/`pj2` — `pp_lp.ml`). A bad token there used to skip the
`_` char-by-char (a warning per occurrence); engine stderr `warning:` lines are
folded with a `(×N)` count so they never bury the real error.

## PP limitations (when authoring goals)

- **BOOL membership**: PP can't reason about `a: BOOL` abstractly. Use
  `btrue`/`bfalse` only as concrete terms in equalities.
- **Cascaded `=>`** is left-associative: `(p=>q) => (r=>s) => g` parses as
  `((p=>q) => (r=>s)) => g`. Use `and` for independent hypotheses.
- **Set-theoretic surface**: `eql_set`, pair decomposition, and HO set operators
  aren't in the goal-formula syntax.
- **Arithmetic**: AR1–AR13 reduce to `B.lp`'s integer primitives; some emitted
  proofs carry `trust` for solver-level conjuncts.

## Admits / trust

- **`lp/B.lp:17` — `symbol trust : π P`.** Intentional; the only declared
  `axiom`/`admit` in `lp/`.
- **Emitted `trust` at use sites.** The emitter passes `trust` for inline
  side-condition arguments where PP's check is solver-confirmed rather than
  tracked (BOOL membership, INS arithmetic-match conjuncts, AR2/AR4/AR5/AR6/
  AR10/AR13 side conditions). It must NOT emit a whole-goal `refine trust;`.
- **Unsupported shapes.** `rule_emit.ml` / `translate.ml` `failwith` rather than
  emit a whole-goal `trust` (e.g. AR7/AR8). New shapes get an explicit `emit`
  constructor in `rule_db.ml` plus its dispatch arm.

## Replay format

```
 [RULE] <formula>          base rule, with per-rule annotation
 [RULE(arg)] <formula>     argument in parens (subscript / hyp / pred)
 [RULE_1] <formula>        primed variant (Res-typed)
 [RULE_N] <formula>        n-ary, binder count N
 [FIN(predicate)] …        phantom (normalisation result)
 [STOP_NORM] / [NRM] …     phantom
```

Main sequent proof is prefix-style (rule before children). The result-chain
child of a branching quantifier is emitted *before* the branch rule (postfix
within the chain). The first non-phantom line's annotation is the overall goal.
`Rule_db.is_phantom` filters phantoms; `Proof_tree.build` reconstructs the tree
replay-natively. Unknown rule names raise.

## Common errors

| Error                                                  | Where                              | Fix                                                                |
|--------------------------------------------------------|------------------------------------|--------------------------------------------------------------------|
| `rule_db: unknown rule "X"`                            | `proof_tree.ml`/`rule_db.ml`       | Add `X` to `rule_db.ml` (arity / phantom / hoas_identity).        |
| `rule_db: X unsupported arity N`                       | `proof_tree.ml`                    | Review the rule's slot kinds in `rule_db.ml`.                      |
| `translate: X arity N unsupported`                     | `translate.ml`                     | New rule shape needs a dispatch arm.                               |
| `tree-build error: replay left N unconsumed rule lines`| `proof_tree.ml`                    | An earlier rule has the wrong arity; `PP2LP_DEBUG_REPLAY=1` traces the build. |
| `tree-build error: X expected a child but stack is empty` | `proof_tree.ml`                 | Wrong arity for an earlier rule.                                   |
| `parse error in PATH: …`                               | `parser.mly` / `parse_replay.ml`   | Bad replay line; inspect the column reported.                      |
| `File X.lpo is incompatible with current binary`       | lambdapi                           | `git clean -Xf lp/bench`.                                          |
| `package X cannot be mapped under the library root`    | lambdapi                           | Missing `lambdapi.pkg`. `lp/lambdapi.pkg` covers the whole package. |

## Suites

- **og** — 30 traces checked in, the baseline smoke test. No `.but` files (the
  traces are the source of truth).
- **prv** — Atelier B PRV corpus. `.but` checked in; `.trace`/`.replay`
  gitignored. Green (70 ✓).
- **prv-no-arith** — non-arithmetic subset of prv, to isolate translation/proof
  failures without arithmetic-solver noise.
- **synth** / **nrm_test** / **gemini** — synthetic suites generated from a
  `goals.txt` (`name | kind | goal`) by `pp2lp gen SUITE`. Each goal is proved
  from itself plus inferred `_delta_{e,p}` hypotheses; the generator is
  binder-aware (bound `!x`/`#x` vars get no delta). **`goals.txt` is the source
  of truth** — generation rewrites *every* benchmark dir, so add goals there, not
  as loose files; removing a goal removes its dir. nrm_test's `COVERAGE.md` maps
  each NRM rule → goal. Any failing goal ⇒ exit 1.
- **claude** — a hand-authored *pipeline stress / coverage* suite (same
  `goals.txt` mechanism), not a green gate: it spans every rule family + proof
  sizes 1→416 replay lines and probes the failure frontier on purpose (sections
  L–P are expected ✗/⚠). 233 goals → 85/93 rules exercised. Used to find bugs;
  inline notes flag each frontier blocker. **`#` existentials are allowed** in
  goals.txt (the comment splitter no longer eats `#x`).

## Commits

No `Co-Authored-By`. No Claude / Anthropic attribution.

## Where to start

- New PP rule in a replay: `ocaml/src/rule_db.ml` (add the rule + its `emit`
  strategy; the exhaustive match in `rule_emit.ml` then *forces* a dispatch arm).
- Emit bug — pick the layer:
  - wrong `refine` arguments → `ocaml/src/rule_emit.ml`;
  - wrong tree structure (sequence/assume/branch, main vs Res-chain) →
    `ocaml/src/translate.ml`;
  - hypothesis / witness / INS search → `ocaml/src/emit_ctx.ml`.
- LP-side proof gap: `lp/rules/*.lp` (the rule lemmas) + the rule recap in
  `doc/pp-spec-rules.pdf`.
- Replay format itself: top of `parse_replay.ml` + `proof_tree.ml`.
- The CLI / loop tooling: `./pp2lp` (one self-contained Python file).
