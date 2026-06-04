# CLAUDE.md

Maintainer notes for **pp2lp** — translates Atelier B Predicate Prover
(PP) proof replays to Lambdapi for independent type-checking.

Round trip: `formula → PP → .trace → REPLAY → .replay → pp2lp → .lp → lambdapi check`.

One command does everything: **`pp2lp run`** (the executable `./pp2lp` at the
repo root). It builds the OCaml engine, emits Lambdapi, type-checks it, and
reports — for a whole suite (exit non-zero if any benchmark fails) or one
trace (a detailed per-trace report). The OCaml binary under `ocaml/_build/` is
an internal engine; you drive `./pp2lp`.

The generated `.lp` has no comments. Instead the engine writes a separate table
mapping each `.lp` line to the PP rule, replay line, and goal that produced it.
When Lambdapi reports an error on a line, `pp2lp` looks it up in that table and
shows three things side by side: the `.lp` at the error, the `.replay` step it
came from, and the matching `lp/rules/` lemma.

## Commands

```
pp2lp run                       # check the og suite
pp2lp run synth                 # check a suite (any ✗ ⇒ exit 1)
pp2lp run og/01                 # check one trace; a failure shows snippet panels
pp2lp run synth/x               # failure → .lp + .replay + lp/rules snippet panels
pp2lp run synth/x --lp-debug=u  # also probe lambdapi (debug +u) → a .lp.debug panel
pp2lp run og --json             # machine output (also bench/results/og.json)
pp2lp run og -q                 # summary only (suppress failure windows)

pp2lp gen synth                 # (re)gen .but/.trace/.replay via krt (PP/REPLAY)
pp2lp gen prv --only replays    # one stage only (buts,traces,replays)
```

`run` auto-builds the engine first (`--no-build` to skip). Suites run in
parallel (the shared `lp/` objects are compiled once up front, so a cold run
doesn't race); per-trace outcome is `✓` / `⚠` / `✗`, and exit status is
non-zero iff any trace fails. Suites: `og` (default), `prv`, `prv-no-arith`,
`synth`, `nrm_test`.

Child-process caps (env-tunable, 0 disables): `PP2LP_CHECK_TIMEOUT` (60s),
`PP2LP_EMIT_TIMEOUT` (30s), `PP2LP_CHECK_MEM_GB` (4 GiB `RLIMIT_AS`).

### The engine (internal)

`pp2lp run` shells out to the OCaml engine at
`ocaml/_build/default/bin/main.exe` (the `emit` subcommand) and to
`lambdapi`; `pp2lp gen` shells out to Atelier B's `krt`. You never call them
directly — `pp2lp` handles package paths, the error→rule lookup, the pass/fail
exit status, and the safety caps for you.

## Mental model

PP is Atelier B's automated first-order prover. A `.but` file (formula
+ flags) becomes a `.trace` (postorder), then Atelier B's REPLAY tool
turns that into a `.replay`: sequent proof nodes are emitted prefix-style
(rule before child subproofs), and the result-chain child of a branching
quantifier (ALL7 / XST8) is emitted *before* the branch rule itself.
Each line carries the per-rule formula annotation PP saw when it applied
that rule.

`pp2lp` parses the replay, rebuilds the tree (`proof_tree.ml`), and
emits an `opaque symbol` whose body is a tactic script — each PP rule
becomes a `refine RULE …` against a lemma in `lp/rules/`. Lambdapi then
type-checks the symbol.

Three rule shapes, decoded by `Rule_db.strip_suffix` / `is_primed`:

- **base** — `[AND2]`. Plain LP refine.
- **`_1` primed** — `[AND2_1]`. Inside a Res-typed equality chain
  preceding a branching quantifier.
- **`_N` n-ary** — `[ALL7_2]`, `[NRM1_3]`. Binder count = N.

Branching rules (`ALL7`, `XST8`) are two-child: a Res-typed chain plus
a continuation under the bound variable.

`rule_db.ml` is the **single source of truth** for rule metadata —
arity, suffix decoding, phantom-rule predicate, and the **emit strategy**:
a typed `emit` variant (`Default | Trust_cons | Hyp_search | Witness_hyp |
Ins | And5 | Opr of bool | Axm8 | Nrm20 | Nrm22 | Ar3 | Ar4 | Ar5_6 |
Ar7_8 | Ar9 | Ar10`). `rule_emit.ml` matches that variant **exhaustively**,
and warning 8 (partial-match) is fatal — so a new rule that adds a
constructor *must* get a handling arm or the build breaks. (This replaced a
stringly-typed `emit_args : string option` whose dangling `dynamic:ar4`-style
tags silently fell through to a wrong default.) Don't reimplement substring
checks or `base rule = "…"` dispatch elsewhere. Unknown rule names are
*errors*, not phantoms: `is_phantom` raises `Failure "rule_db: unknown rule …"`.

## Source layout

```
ocaml/src/           (core modules carry .mli interfaces)
  lexer.mll          lex bracketed rule lines + annotations
  parser.mly         parse them
  parse_replay.ml    .replay file → rules list
  rule_db.ml         rule metadata: arity, suffix, phantom, emit strategy
                     (the typed `emit` variant — the single dispatch key)
  proof_tree.ml      rules list → proof tree (replay-native rebuild)
  syntax_pp.ml       PP-side AST
  free_vars.ml       collect free Prop / τ ι vars for the symbol header
  emit_ctx.ml        emission context (ctx) + hyp/witness/INS searches
  rule_emit.ml       per-rule `refine` tactic construction — exhaustive
                     match on rule_db's `emit`
  translate.ml       proof_tree → lp_tree: the tree walker (structure:
                     sequence / assume / branch; main + Res-chain)
  lp_tree.ml         LP tactic-script AST
  pp_lp.ml           pretty-printer: PP AST → LP source
  emit_pp.ml         PP-side encoding
  emit_lp.ml         emit_symbol wrapper + lp_header
  reconstruct.ml     parse_replay → proof_tree → emit_symbol
ocaml/bin/main.ml    CLI: emit

lp/
  lambdapi.pkg       package_name = pp2lp
  B.lp               B-Book primitives + the intentional `trust` axiom (line 17)
  ConjList.lp        n-ary conjunction (⋀) abstraction layer
  Rules.lp           top-level require-open for all rule files
  Quant.lp           quantifier helpers (!! ?? ♢ ♡)
  rules/*.lp         per-section: All, Arith, Axm, Bool, Conj, Disj,
                     Eq, Equiv, Impl, Neg, Nrm, Res, TrueFalse, Xst
  bench/<suite>/<name>/   per-benchmark dir: <name>.{but,trace,replay,lp,lpo}
                     + the <name>.lp.debug probe trace (.lp/.lpo/.lp.*
                     gitignored; og's .trace/.replay are tracked)

pp2lp                the single CLI (Python): `pp2lp run` — emit, check, gen,
                     audit, and every debug lens. Wraps the engine + lambdapi
                     + krt; replaces the former Makefile + bench/*.py helpers.
bench/
  results/           per-run JSON result artifacts (gitignored)

doc/
  spec_pp.md         PP specification (translated)
  rules.md           per-rule LP status table
  b-book-ref.md      B-Book pointers
```

## Workflows

### Iterating on the emitter

After editing OCaml source, `pp2lp run og/01` (it rebuilds first). On failure
the lambdapi diagnostic gets ±3 lines of source context pointing into the
emitted `lp/bench/SUITE/NAME/NAME.lp`, with the originating PP rule and replay
step shown under each error.

### Debugging a failing trace

`pp2lp run SUITE/NAME` on a single trace — and `pp2lp run SUITE` for *every*
failing trace in a suite — prints the **failure window**: one numbered code
snippet per related file, each headed by its `filename:position` with the
relevant line marked `>`. The files are the emitted `.lp` at the error line, the
`.replay` proof step that produced it, and the failing rule's `lp/rules/*.lp`
type signature — so the rule name and the goal PP saw are surfaced by the
snippets themselves. In a suite each benchmark gets a heavy `━━` header so the
blocks are clearly separated. There is no `-v`; the window is the default — `-q`
suppresses it for a clean gate.

- `--lp-debug=CODE` adds a **scoped** lambdapi probe: it injects `debug +CODE;`
  immediately before the failing tactic (CODE is raw lambdapi flags —
  `u`=unification, `r`=rewrite, `t`=tactics, `w`=whnf; bare `--lp-debug` ⇒ `u`),
  runs the check, and writes the cleaned trace (the `[tag] …` lines minus the
  giant `solve {…}` dumps) next to the `.lp` as `<name>.lp.debug` — surfaced,
  full and untruncated, as an extra snippet; stale traces are cleared each run.
  Avoid `i` — type inference crashes lambdapi's printer on our HO goals.

An emit-side `Failure` → `translate.ml` / `proof_tree.ml` / `parse_replay.ml`;
the report prints a stable error code (`E_UNKNOWN_RULE`, `E_ARITY`,
`E_DISPATCH`, `E_TREE_BUILD`, `E_PARSE`, …) and a next-step hint. The replay→tree
state machine is available via `PP2LP_DEBUG_REPLAY=1`.

### Inspecting LP goals / debugging LP rules

Use the **sibling-probe** convention — create `lp/rules/Foo_probe.lp`:

```
require open pp2lp.B pp2lp.rules.Foo;
print FOO_LEMMA;
compute SOME_TERM;
```

and `lambdapi check` it. To inspect a proof's mid-state, copy the emitted
`lp/bench/SUITE/NAME/NAME.lp` and insert `print; proofterm;` before a tactic —
or run `pp2lp run SUITE/NAME --lp-debug=u` for the scoped lambdapi trace
(written beside the `.lp` as `NAME.lp.debug`). **Delete probe
files when done.** Clear stale emitted artifacts with
`git clean -Xf lp/bench bench/results`.

### Adding a corpus trace

1. Drop `lp/bench/SUITE/name/name.but` (or add a line to synth `goals.txt`).
2. `pp2lp gen SUITE` — runs PP/REPLAY (krt) to build `.trace`/`.replay`; a
   truncated replay is dropped here, with a warning.
3. `pp2lp run SUITE/name` — emit + type-check.

### Pre-commit audit

1. `pp2lp run og` must pass (30 ✓, exit 0). `synth`/`nrm_test` are strict too
   (non-zero while any goal fails — expected; see Known broken).
2. `rg -n '\badmit\b' lp/ | rg -v 'B.lp:17'` — must print nothing. Only the
   `trust` axiom at `lp/B.lp:17` may be an admit; this catches a multi-line
   `begin … admit … end` that the old single-line pattern missed.
3. `rg 'refine trust;\s*$' lp/bench/og/` — no whole-goal `trust` in emitted og.
   Inline `trust` as a refine *argument* is fine and documented; a bare
   `refine trust;` means the emitter gave up.
4. No stray probe files (`*_probe.lp`, `*_test.lp`, `*_dbg.lp`) under `lp/`.

The prv suite is exempt — see below.

## Known broken

- **prv suite: 27 ✓ / 43 ✗ of 70.** (No longer all-fail; the former
  `INST_FINAL` three-piece-pipe and stack-residual issues no longer occur.)
  Remaining failures, by cause:
  - **INS contradiction over arithmetic-rewritten hyps (~31).** PP's solver
    rewrites the hypotheses (`e-f-x≤0` …) before the INS leaf, so
    `find_ins_contradiction` (`emit_ctx.ml`) finds no structural match —
    emit fails (`E_INS`); or it finds the wrong compound witness for an
    NRM20-normalised universal and lambdapi rejects the `!!_to_pi` evidence
    (the 6 `subset_*` lp-check failures).
  - **AR7/AR8 (eq_018, eq_019).** Need the solver's witness (the `a` in
    `a + c = 𝟎`), which the replay never records. `rule_emit.ml` now
    `failwith`s here explicitly instead of emitting an ill-typed `refine`.
  - **AR4 deeper cases (leq_003/005/009, eq_017).** The AR4 emit itself is
    fixed (see leq_004), but these hit a `neg_neg` gap: PP normalises
    `𝟏 - (—a)` to `1+a` while the LP AR3 rule keeps it literal, leaving a
    `prj 0 x ≡ —(—(prj 0 x))` constraint unsolved.
  `pp2lp run prv` exits non-zero while any goal fails — not yet a clean gate.

- **synth suite: 7 failures.** `pp2lp run synth`
  exits non-zero while any goal fails. Current: 100 ✓ /
  7 ✗ of 107 goals. REPLAY-truncated goals are no longer here — `gen` drops a
  truncated replay at generation time (with a warning), so it never reaches the
  suite.
  - ConjList/`Res` snoc-refactor incompleteness (`rel_partial_func`,
    `rel_total_inj`, `rel_total_surj`, `rel_bijection`, `subset_pow`): an `ALL7`
    continuation's `res_tm` over a simple `STOP_1` chain doesn't resolve the
    universal predicate via HO-unification, breaking NRM14 and the INS
    contradiction (functional-uniqueness goals hit this hard).
    `--lp-debug=u` shows the unsolvable `Res … ≡ ⊥` constraint.
  - `ar_add_shape` — proves an equality via ≤-antisymmetry, reaching `AR7`/`AR8`,
    which need solver witness values (the `a` in `a + c = 𝟎`) not recorded in
    the replay. Deeper than the env/trust AR fixes below.
  - `ar_in_nat` (`n: NAT`) — NAT membership sends lambdapi into a memory blowup,
    killed fast by the `RLIMIT_AS` cap (it fails, it doesn't hang).

  The two AR emit bugs that previously bit `AR9`/`AR3` are now fixed:
  rule value-arguments are rendered through the tuple-projection env
  (`translate.ml` `render_exp_term`/`render_pred_term`, used by
  `dynamic_value_args`), and `AR9`'s solver-confirmed `E = F` premise is
  supplied as `trust` (`metadata_extra_args`). This fixed `ar_leq_trans_hyp`.

- **Benchmark safety caps.** `pp2lp run` bounds every child process so a
  runaway goal can't take down the host: a wall-clock timeout and (POSIX) an
  `RLIMIT_AS` address-space + `RLIMIT_CPU` cap. Tunable via env —
  `PP2LP_CHECK_TIMEOUT` (lambdapi, default 60s), `PP2LP_EMIT_TIMEOUT` (pp2lp,
  30s), `PP2LP_CHECK_MEM_GB` (default 4). The `gen` krt runs time out too.

## PP limitations

Show up regularly when authoring goals:

- **BOOL membership**: PP can't reason about `a: BOOL` abstractly.
  Use `btrue` / `bfalse` only as concrete terms in equalities.
- **Cascaded `=>`**: PP's `=>` is left-associative.
  `(p => q) => (r => s) => g` parses as `((p => q) => (r => s)) => g`.
  Use `and` for independent hypotheses.
- **Set-theoretic surface**: `eql_set`, pair decomposition, and
  higher-order set operators aren't in the goal-formula syntax.
- **Arithmetic**: AR1–AR13 reduce to `B.lp`'s integer primitives;
  some emitted proofs carry `trust` for solver-level conjuncts.

## Admits / trust categories

- **`lp/B.lp:17` — `symbol trust : π P`.** Intentional. The only
  declared `axiom`/`admit` in `lp/`.
- **Emitted `trust` at use sites.** The emitter passes `trust` for
  inline side-condition arguments where PP's check is solver-confirmed
  rather than tracked. It must NOT emit a whole-goal `refine trust;`.
  Categories (see `doc/rules.md`):
  - BOOL31–42 — `V ϵ BOOL` membership
  - INS arithmetic-match conjuncts
  - AR2, AR10, AR13 — solver-confirmed side conditions
  - AR4 — the `(E+F) > 𝟎` conjunct (F recovered from an in-scope `F ≤ 𝟎`
    hyp); AR5/AR6 — the `±a ≤ 𝟎` solver premise
- **Unsupported shapes.** The emitter (`rule_emit.ml` / `translate.ml`)
  `failwith`s rather than emit a whole-goal `trust` — e.g. AR7/AR8, whose
  solver witness the replay omits. New shapes get an explicit `emit`
  constructor in `rule_db.ml` plus its dispatch arm.

## Replay format

```
 [RULE] <formula>                  base rule, with per-rule annotation
 [RULE(arg)] <formula>             argument in parens (subscript / hyp / pred)
 [RULE_1] <formula>                primed variant (Res-typed)
 [RULE_N] <formula>                n-ary, binder count N
 [FIN(predicate)] <FIN(…)>         phantom (normalisation result)
 [STOP_NORM] <formula>             phantom
 [NRM] <formula>                   phantom
```

Main sequent proof is prefix-style (rule before its children). The
result-chain child of a branching quantifier is emitted *before* the
branch rule (postfix within the chain). The first non-phantom line's
annotation is the overall goal. `Rule_db.is_phantom` filters phantoms;
`Proof_tree.build` reconstructs the tree replay-natively. Unknown rule
names raise.

## Common errors

| Error                                                  | Where                              | Fix                                                                |
|--------------------------------------------------------|------------------------------------|--------------------------------------------------------------------|
| `rule_db: unknown rule "X"`                            | `proof_tree.ml`/`rule_db.ml`       | Add `X` to `rule_db.ml` (arity / phantom / hoas_identity).        |
| `rule_db: X unsupported arity N`                       | `proof_tree.ml`                    | Review the rule's slot kinds in `rule_db.ml`.                      |
| `translate: X arity N unsupported`                     | `translate.ml`                     | New rule shape needs a dispatch arm.                               |
| `tree-build error: replay left N unconsumed rule lines`| `proof_tree.ml`                    | an earlier rule has the wrong arity; set `PP2LP_DEBUG_REPLAY=1` to trace the build. |
| `tree-build error: X expected a child but stack is empty` | `proof_tree.ml`                 | Wrong arity for an earlier rule.                                   |
| `parse error in PATH: …`                               | `parser.mly` / `parse_replay.ml`   | Bad replay line; inspect the column reported.                      |
| `File X.lpo is incompatible with current binary`       | lambdapi                           | `git clean -Xf lp/bench`.                                          |
| `package X cannot be mapped under the library root`    | lambdapi                           | Missing `lambdapi.pkg`. `lp/lambdapi.pkg` covers the whole package. |

## Suites

- **og** — 30 traces checked in. The baseline smoke test. No `.but`
  files (the traces are the source of truth).
- **prv** — Atelier B PRV corpus. `.but` checked in; `.trace` and
  `.replay` gitignored. Currently all-fail; see Known broken.
- **prv-no-arith** — Non-arithmetic subset of the PRV suite. Used to
  isolate and debug translation and proof failures without arithmetic
  solver noise.
- **synth** — Synthetic `.but` files for targeted feature testing, generated
  from `lp/bench/synth/goals.txt` (`name | kind | goal`) by
  `pp2lp gen synth --only buts`. Each goal is proved from itself plus inferred
  `_delta_{e,p}` hypotheses; the generator is binder-aware (bound `!x`/`#x`
  vars get no delta). `goals.txt` is the source of truth — generation rewrites
  *every* benchmark dir, so add goals there, not as loose files; a goal removed
  from `goals.txt` has its `synth/<name>/` dir removed too. After editing:
  `pp2lp gen synth`, then `pp2lp run synth`. Any failing goal ⇒ exit 1 (see Known
  broken for the current failures).
- **nrm_test** — NRM-rule coverage suite, same `goals.txt` mechanism as synth
  (generate with `pp2lp gen nrm_test`). Goals are chosen so promoting the
  goal-as-hypothesis fires a target NRM rule; `COVERAGE.md` maps each rule →
  goal and tracks the implemented rules currently reached. Any failing goal ⇒
  exit 1. **Caution:** never loop raw `lambdapi check` over its `.lp` — the
  `x: NAT` goals OOM the host; use `pp2lp run nrm_test`, which applies the
  child-process caps (`RLIMIT_AS` kills the blowup fast).

## Commits

No `Co-Authored-By`. No Claude / Anthropic attribution.

## Where to start

- New PP rule in a replay: `ocaml/src/rule_db.ml` (add the rule + its
  `emit` strategy; the exhaustive match in `rule_emit.ml` then *forces* you
  to give it a dispatch arm).
- Emit bug — pick the layer:
  - wrong `refine` arguments → `ocaml/src/rule_emit.ml`;
  - wrong tree structure (sequence / assume / branch, main vs Res-chain) →
    `ocaml/src/translate.ml` (provenance stamped per node by `prov_of`,
    rendered out-of-band by `Lp_tree.Commented`);
  - hypothesis / witness / INS search → `ocaml/src/emit_ctx.ml`.
- LP-side proof gap: `lp/rules/*.lp` + `doc/rules.md`.
- Replay format itself: top of `parse_replay.ml` + `proof_tree.ml`.
- The CLI / loop tooling: `./pp2lp` (one self-contained Python file).
