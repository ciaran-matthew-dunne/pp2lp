# CLAUDE.md

Maintainer notes for **pp2lp** — translates Atelier B Predicate Prover
(PP) proof replays to Lambdapi for independent type-checking.

Round trip: `formula → PP → .trace → REPLAY → .replay → pp2lp → .lp → lambdapi check`.

The pp2lp binary translates one replay; everything else (emit + check +
format + loop over a suite) is wired together by the Makefile and a few
small Python helpers under `bench/`.

## Commands

```
make                       # help
make build                 # dune build for ocaml/
make check                 # og suite (default)
make check og              # og suite
make check prv             # prv suite
make check og/01           # one replay
make tree  og/27           # rebuilt proof tree (residual on failure)
make rules og/22           # parsed (rule, arg, kind) listing
make check og V=1          # verbose output
make check og Q=1          # summary only
make gen-traces prv        # .but → .trace (runs PP)
make gen-replays prv       # .trace → .replay (debug-only)
make clean-bench           # lp/bench/ + lp/**/*.lpo
make clean                 # also dune clean
make repl                  # dune utop with project loaded
```

Suites: `og` (default), `prv`, `prv-no-arith`, `synth`. `PP2LP_ROOT`
is exported so symlinked checkouts work.

### The pp2lp binary directly

```
pp2lp emit  REPLAY  # LP on stdout
pp2lp tree  REPLAY  # rebuilt proof tree (on failure: residual stack)
pp2lp rules REPLAY  # parsed (rule, arg, kind) lines, flags UNKNOWN rules
pp2lp REPLAY        # alias for `emit`
```

Outcomes per replay: `✓` (pass), `⚠` (pass with warnings), `✗` (fail).
Exit status is non-zero iff any fail.

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
  reconstruct.ml     parse_replay → proof_tree → emit_lp
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

bench/
  _krt.py            shared helper module for krt-based generators
  check.py           emit + lambdapi-check orchestrator
  gen_traces.py      .but → .trace (PP runner)
  gen_replays.py     .trace → .replay (REPLAY runner; debug only)
  format_lambdapi_json.py    pretty-print `lambdapi check --json` output,
                             ±3 lines of source context per error
  og/                30 traces checked in (no .but files)
  prv/               Atelier B PRV corpus. .but checked in; .trace and
                     .replay gitignored. Currently all-fail — see
                     "Known broken" below.

doc/
  spec_pp.md         PP specification (translated)
  rules.md           per-rule LP status table
  b-book-ref.md      B-Book pointers
```

## Workflows

### Iterating on the emitter

`make build` is fast. Run `make build` after editing OCaml source,
then `make check` or `make check og/01` to test.

Single-trace round trip: `make check og/01`. Output is `✓` / `✗`
with detail on failure. The lambdapi diagnostic gets ±3 lines of
source context pointing into `lp/bench/SUITE/NAME.lp`.

### Debugging a failing trace

Order of escalation:

1. `make check og/01` — see the lambdapi error in source context.
2. `make tree  og/01` — see the rebuilt proof tree (or the residual
   stack if the rebuild itself failed).
3. `make rules og/01` — dump the parsed `(rule, arg, kind)` lines.
   Look for `UNKNOWN`: that means `rule_db.ml` is missing an entry.
4. `Read lp/bench/SUITE/NAME.lp` — the emitted file, at the reported
   `offset`. Files can be large; use `offset` / `limit`.
5. Emit-side OCaml exception → `translate.ml` / `proof_tree.ml` /
   `parse_replay.ml`. Match the message against those.

### Inspecting LP goals / debugging LP rules

No pp2lp subcommand for this — use the **sibling-probe** convention.
Create `lp/rules/Foo_probe.lp` (or anywhere under `lp/`):

```
require open pp2lp.B pp2lp.rules.Foo;
print FOO_LEMMA;
compute SOME_TERM;

// or inside a proof, before the failing tactic:
opaque symbol _probe : π P ≔
begin
  print;       // dumps hypotheses + current goal
  proofterm;   // dumps the partial proof term
end;
```

Run `lambdapi check lp/rules/Foo_probe.lp`. **Delete when done** —
probe files must not be committed. `*.lpo` is gitignored; run
`make clean-bench` if stale `.lpo` files cause compatibility errors.

For scoped traces, wrap a region in `debug +u;` / `debug -u;` (or `+a`
for all).

### Adding a corpus trace

1. Drop `name.but` in `lp/bench/SUITE/`.
2. `make gen-traces SUITE` — runs PP, writes `name.trace`.
3. `make check SUITE/name` — emit + lambdapi check.

### Pre-commit audit

1. `make check` — verify all pass.
2. `Grep '≔ begin admit end' lp/` — only `lp/B.lp:17` (`trust`)
   should match.
3. `Grep 'refine trust;\s*$' lp/bench/og/` — no whole-goal `trust`
   in any emitted file. Inline `trust` (as an argument to a refine)
   is fine and documented; a bare `refine trust;` means the emitter
   gave up.
4. No probe files (`*_probe.lp`, `*_test.lp`, `*_experiment.lp`)
   under `lp/`.

The prv suite is exempt — see below.

## Known broken

- **prv suite: 100% fail.** Two distinct issues:
  - `INST_FINAL(pred | exp | FAUX)` — three-piece pipe argument,
    parser only knows the two-piece form (`parser.mly:106-110`).
  - Several traces (e.g. `eq_020`) leave many nodes on the stack —
    `make tree prv/eq_020` shows the residual.
  Don't run `make check prv` as a gate until these are fixed.

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
| `tree-build error: replay left N unconsumed rule lines`| `proof_tree.ml`                    | `make tree SUITE/NAME` shows the residual; an earlier rule has wrong arity. |
| `tree-build error: X expected a child but stack is empty` | `proof_tree.ml`                 | Wrong arity for an earlier rule.                                   |
| `parse error in PATH: …`                               | `parser.mly` / `parse_replay.ml`   | Bad replay line; inspect the column reported.                      |
| `File X.lpo is incompatible with current binary`       | lambdapi                           | `make clean-bench`.                                                |
| `package X cannot be mapped under the library root`    | lambdapi                           | Missing `lambdapi.pkg`. `lp/lambdapi.pkg` covers the whole package. |

## Suites

- **og** — 30 traces checked in. The smoke-test floor. No `.but`
  files (the traces are the source of truth).
- **prv** — Atelier B PRV corpus. `.but` checked in; `.trace` and
  `.replay` gitignored. Currently all-fail; see Known broken.
- **prv-no-arith** — Non-arithmetic subset of the PRV suite. Used to
  isolate and debug translation and proof failures without arithmetic
  solver noise.
- **synth** — Synthetic `.but` files for targeted feature testing.

## Commits

No `Co-Authored-By`. No Claude / Anthropic attribution.

## Where to start

- New PP rule in a replay: `ocaml/src/rule_db.ml`.
- Emit bug: `ocaml/src/translate.ml`.
- LP-side proof gap: `lp/rules/*.lp` + `doc/rules.md`.
- Replay format itself: top of `parse_replay.ml` + `proof_tree.ml`.
