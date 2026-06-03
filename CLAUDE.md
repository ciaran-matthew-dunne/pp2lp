# CLAUDE.md

Maintainer notes for **pp2lp** — translates Atelier B Predicate Prover
(PP) proof replays to Lambdapi for independent type-checking.

Round trip: `formula → PP → .trace → REPLAY → .replay → pp2lp → .lp → lambdapi check`.

One command does everything: **`pp2lp run`** (the executable `./pp2lp` at the
repo root). It builds the OCaml engine, emits Lambdapi, type-checks it, and
reports — for a whole suite (a deviation gate) or one trace (a dossier). The
OCaml binary under `ocaml/_build/` is an internal engine; you drive `./pp2lp`.

The generated `.lp` is kept **clean** (no comments).  Alongside it the engine
writes a side-channel `line → rule, replay-line, goal` map, so a Lambdapi error
resolves straight back to its originating PP rule, its replay line, and the
goal PP saw — the *provenance join*, shown in the failure panel together with
code snippets from the related files (`.replay`, `.lp`, the `lp/rules/` lemma).

## Commands

```
pp2lp run                       # check the og suite (default gate)
pp2lp run synth                 # check a suite (deviation gate vs expected_fail.txt)
pp2lp run og/01                 # check one trace; a failure shows snippet panels
pp2lp run synth/x               # failure → .lp + .replay + lp/rules-signature panels
pp2lp run synth/x --debug       # …also add the scoped lambdapi unification trace
pp2lp run og --json             # machine output (also bench/results/og.json)
pp2lp run og -q                 # summary only

pp2lp gen synth                 # (re)gen .but/.trace/.replay via krt (PP/REPLAY)
pp2lp gen prv --only replays    # one stage only (buts,traces,replays)
```

`run` auto-builds the engine first (`--no-build` to skip). Suites run in
parallel; per-trace outcome is `✓` / `⚠` / `✗`, and exit status is non-zero
iff a suite deviates from its baseline. Suites: `og` (default), `prv`,
`prv-no-arith`, `synth`, `nrm_test`.

Child-process caps (env-tunable, 0 disables): `PP2LP_CHECK_TIMEOUT` (60s),
`PP2LP_EMIT_TIMEOUT` (30s), `PP2LP_CHECK_MEM_GB` (4 GiB `RLIMIT_AS`).

### The engine (internal)

`pp2lp run` shells out to the OCaml engine at
`ocaml/_build/default/bin/main.exe` (subcommands `emit | tree | rules`) and to
`lambdapi`; `pp2lp gen` shells out to Atelier B's `krt`. You never call them
directly — `pp2lp` handles package paths, the provenance scan, the deviation
gate, and the safety caps for you.

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
arity, suffix decoding, phantom-rule predicate. Don't reimplement
substring checks elsewhere. Unknown rule names are *errors*, not
phantoms: `is_phantom` raises `Failure "rule_db: unknown rule …"`.

## Source layout

```
ocaml/src/
  lexer.mll          lex bracketed rule lines + annotations
  parser.mly         parse them
  parse_replay.ml    .replay file → rules list
  rule_db.ml         rule metadata: arity, suffix, phantom, emit-args
  proof_tree.ml      rules list → proof tree (replay-native rebuild)
  syntax_pp.ml       PP-side AST
  free_vars.ml       collect free Prop / τ ι vars for the symbol header
  translate.ml       proof_tree → lp_tree (the dispatch heart)
  lp_tree.ml         LP tactic-script AST
  pp_lp.ml           pretty-printer: PP AST → LP source
  emit_pp.ml         PP-side encoding
  emit_lp.ml         emit_symbol wrapper + lp_header
  reconstruct.ml     parse_replay → proof_tree → emit_symbol
ocaml/bin/main.ml    CLI: emit | tree | rules

lp/
  lambdapi.pkg       package_name = pp2lp
  B.lp               B-Book primitives + the intentional `trust` axiom (line 17)
  ConjList.lp        n-ary conjunction (⋀) abstraction layer
  Rules.lp           top-level require-open for all rule files
  Quant.lp           quantifier helpers (!! ?? ♢ ♡)
  rules/*.lp         per-section: All, Arith, Axm, Bool, Conj, Disj,
                     Eq, Equiv, Impl, Neg, Nrm, Res, TrueFalse, Xst
  bench/<suite>/     emitted .lp files (gitignored)

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
emitted `lp/bench/SUITE/NAME.lp`, with the provenance join under each error.

### Debugging a failing trace

`pp2lp run SUITE/NAME` on a single trace prints a failure panel — by default,
the relevant **code snippets**: the lp error location, the PP **rule** whose
tactic spans it (`replay:N`) and that rule's PP **goal**, lambdapi's stuck
state (the goals — never just the hypotheses), and three file snippets — the
emitted `.lp`, the `.replay` proof step, and the failing rule's `lp/rules/*.lp`
type signature.  There is no `-v`; the panels are the default.

- `--debug` — *additionally* run a **scoped** lambdapi probe of the failing
  tactic (`debug +u;`/`-u;`), distilled to the constraint that failed (`A ≡ B`,
  `failed`, `no unif_rule`).  Categories `unif`/`rewrite`/`tactic`/`whnf`, or
  `raw` for the full trace.  These are *our* curated flags — we never expose
  lambdapi's `i` (type inference), which crashes its printer on our HO goals.

An emit-side `Failure` → `translate.ml` / `proof_tree.ml` / `parse_replay.ml`;
the dossier prints a stable error code (`E_UNKNOWN_RULE`, `E_ARITY`,
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
`lp/bench/SUITE/NAME.lp` and insert `print; proofterm;` before a tactic — or
just use `pp2lp run SUITE/NAME --debug`, which does the scoped `debug +u;` /
`debug -u;` wrapping for you. **Delete probe files when done.** Clear stale
emitted artifacts with `git clean -Xf lp/bench bench/results`.

### Adding a corpus trace

1. Drop `name.but` in `lp/bench/SUITE/` (or add a line to synth `goals.txt`).
2. `pp2lp gen SUITE` — runs PP/REPLAY (krt) to build `.trace`/`.replay`.
3. `pp2lp run SUITE/name` — emit + type-check.

### Pre-commit audit

1. `pp2lp run og` (all pass) and `pp2lp run synth` (matches its baseline) —
   both exit non-zero on any deviation.
2. `rg '≔ begin admit end' lp/` — only `lp/B.lp` (the `trust` axiom) may match.
3. `rg 'refine trust;\s*$' lp/bench/og/` — no whole-goal `trust` in emitted og.
   Inline `trust` as a refine *argument* is fine and documented; a bare
   `refine trust;` means the emitter gave up.
4. No stray probe files (`*_probe.lp`, `*_test.lp`, `*_dbg.lp`) under `lp/`.

The prv suite is exempt — see below.

## Known broken

- **prv suite: 100% fail.** Two distinct issues:
  - `INST_FINAL(pred | exp | FAUX)` — three-piece pipe argument,
    parser only knows the two-piece form (`parser.mly:106-110`).
  - Several traces (e.g. `eq_020`) leave many nodes on the stack —
    the engine's `tree` command dumps the residual.
  Don't run `pp2lp run prv` as a gate until these are fixed.

- **synth suite: 8 baselined failures + an `xfail/` set.** `pp2lp run synth`
  is a real gate: it exits 0 when the bulk run's failures exactly match the
  baseline in `lp/bench/synth/expected_fail.txt`, and non-zero on any deviation
  — a *new* failure, or a baselined goal that starts *passing* (a stale entry to
  prune). Current baseline: 98 ✓ / 8 xfail (106 runnable + 8 in `xfail/`).
  - `lp/bench/synth/xfail/` (8 goals) holds the unrunnable ones, each
    `xfail`-tagged in `goals.txt`:
    - REPLAY-tool truncation (`eq_dom`, `eq_ran`, `mixed_func_set`,
      `subset_union_left/right`, `subset_union3_left`, `subset_inter_union`):
      the tool drops the sequent continuation after a branching quantifier,
      so the `.replay` ends at `ALL7`/`XST8` and pp2lp reports "ALL7 replay
      branch has no sequent continuation after its result-chain". Unfixable
      in pp2lp.
    - `ar_in_nat` (`n: NAT`): sends lambdapi into a memory blowup. Caught by
      check.py's caps now (see below) but excluded to keep the run fast.
    The bulk glob is non-recursive so `xfail/` is skipped, but
    `pp2lp run synth/<name>` still finds them by name.
  - 8 fail in the bulk run, baselined in `lp/bench/synth/expected_fail.txt`
    (shown as `✗ … (expected)`; single-trace `pp2lp run synth/<name>` still
    prints the full diagnostic):
    - ConjList/`Res` snoc-refactor incompleteness (`rel_partial_func`,
      `rel_total_inj`, `rel_total_surj`, `rel_bijection`, `subset_literal2`,
      `subset_pow`, `subset_singleton`): an `ALL7` continuation's `res_tm` over
      a simple `STOP_1` chain doesn't resolve the universal predicate via
      HO-unification, breaking NRM14/22 and the INS contradiction. (The NRM20
      fix in b7522b5 resolved `rel_total_func` and `rel_partial_inj`, pruned
      from the baseline.)
    - `ar_add_shape` — proves an equality via ≤-antisymmetry, reaching
      `AR7`/`AR8`, which need solver witness values (the `a` in `a + c = 𝟎`)
      not recorded in the replay. Deeper than the env/trust AR fixes below.

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
- **Unsupported shapes.** `translate.ml` should `failwith` rather than
  emit a whole-goal `trust`. New shapes get explicit dispatch.

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
| `tree-build error: replay left N unconsumed rule lines`| `proof_tree.ml`                    | an earlier rule has the wrong arity; the engine `tree` command dumps the residual. |
| `tree-build error: X expected a child but stack is empty` | `proof_tree.ml`                 | Wrong arity for an earlier rule.                                   |
| `parse error in PATH: …`                               | `parser.mly` / `parse_replay.ml`   | Bad replay line; inspect the column reported.                      |
| `File X.lpo is incompatible with current binary`       | lambdapi                           | `git clean -Xf lp/bench`.                                          |
| `package X cannot be mapped under the library root`    | lambdapi                           | Missing `lambdapi.pkg`. `lp/lambdapi.pkg` covers the whole package. |

## Suites

- **og** — 30 traces checked in. The smoke-test floor. No `.but`
  files (the traces are the source of truth).
- **prv** — Atelier B PRV corpus. `.but` checked in; `.trace` and
  `.replay` gitignored. Currently all-fail; see Known broken.
- **prv-no-arith** — Non-arithmetic subset of the PRV suite. Used to
  isolate and debug translation and proof failures without arithmetic
  solver noise.
- **synth** — Synthetic `.but` files for targeted feature testing, generated
  from `lp/bench/synth/goals.txt` (`name | kind | goal [| xfail]`) by
  `pp2lp gen synth --only buts`. Each goal is proved from itself plus inferred
  `_delta_{e,p}` hypotheses; the generator is binder-aware (bound `!x`/`#x`
  vars get no delta). `goals.txt` is the source of truth — generation rewrites
  *every* top-level `.but`, so add goals there, not as loose files. After
  editing: `pp2lp gen synth` (regenerates `.but`/`.trace`/`.replay`), then
  `pp2lp run synth`. `xfail/` holds the unrunnable goals (see Known broken);
  `expected_fail.txt` baselines the goals that run but don't type-check yet,
  making the suite a deviation gate.

## Commits

No `Co-Authored-By`. No Claude / Anthropic attribution.

## Where to start

- New PP rule in a replay: `ocaml/src/rule_db.ml`.
- Emit bug: `ocaml/src/translate.ml` (provenance is stamped per node in
  `tree`/`chain_tree`; the `/* … */` comment is rendered by `Lp_tree.Commented`).
- LP-side proof gap: `lp/rules/*.lp` + `doc/rules.md`.
- Replay format itself: top of `parse_replay.ml` + `proof_tree.ml`.
- The CLI / loop tooling: `./pp2lp` (one self-contained Python file).
