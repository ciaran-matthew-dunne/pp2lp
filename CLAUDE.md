# CLAUDE.md

Maintainer notes for **pp2lp** — translates Atelier B Predicate Prover (PP)
proof replays to Lambdapi for independent type-checking.

Round trip: `formula → PP → .trace → REPLAY → .replay → pp2lp → .lp → lambdapi check`.

One command does everything: **`./pp2lp`** at the repo root. It builds the
OCaml engine, emits Lambdapi, type-checks it, and reports. The OCaml binary
under `ocaml/_build/` is an internal engine; you drive `./pp2lp`.

If anything in this file disagrees with the code, the code wins — fix this
file in the same commit.

## Ground rules

- **Never `git clean` under `lp/bench` or at the repo root.** The bench tree
  holds ~1 GB of gitignored generated artifacts (`.trace`/`.replay`/`.lp`)
  that take hours of PP/REPLAY time to regenerate. For stale-object errors
  the fix is `find lp -name '*.lpo' -delete` (object caches are cheap).
- **`pp2lp gen` rewrites suites.** `gen <suite>` wipes every benchmark dir
  not in that suite's source of truth (goals.txt / checked-in `.but`s),
  tracked orphans included. Run it only when the task *is* corpus
  generation, never as a debugging reflex.
- **`tex/` is the LPAR-26 paper, not the tool.** Don't touch it, `notes.md`,
  `admin/`, `doc/`, or `vendor/` unless explicitly asked.
- Stage by explicit path (`git add <paths>`); never `git add -A`/`-u` or
  `commit -a` — the working tree routinely carries the maintainer's
  in-flight edits. Commit messages: plain prose, no Co-Authored-By, no
  Claude/Anthropic attribution. Don't push unless asked.
- og / prv / claude must be green at every commit (counts under Gates).
- Probe files (`*_probe.lp`, `*.probe.lp` outside `lp/bench`) are scratch —
  delete them when done.

## Commands

```
pp2lp run                       # check the og suite
pp2lp run claude                # check a suite (any ✗ ⇒ exit 1)
pp2lp run og/01                 # one trace; a failure shows snippet panels
pp2lp run apero --filter 'ap_0016'   # subset of a suite by name regex
pp2lp run claude/x --lp-debug=u # also probe lambdapi (debug +u) → .lp.debug panel
pp2lp run og --json             # machine output (also bench/results/og.json)
pp2lp run og -q                 # summary only (suppress failure windows)

pp2lp gen claude                # (re)gen .but/.trace/.replay via krt (PP/REPLAY)
pp2lp gen prv --only replays    # one stage only (buts,traces,replays)
pp2lp gen apero                 # convert+prove the CLEARSY POG corpus (see Suites)

pp2lp audit                     # static pre-commit gate (see Gates); --full adds suites
```

`run` auto-builds the engine first (`--no-build` to skip). Suites run in
parallel; shared `lp/` objects compile once up front. Per-trace outcome is
`✓` / `⚠` / `✗`; exit non-zero iff any trace fails. A failing suite run ends
with a histogram of failures by error code.

Child-process caps (env-tunable, 0 disables): `PP2LP_CHECK_TIMEOUT`,
`PP2LP_EMIT_TIMEOUT`, and `PP2LP_GEN_TIMEOUT` (krt PP/REPLAY) all default to
10 s (the slowest prv trace needs ~7.4 s; tighter defaults turn prv red);
`PP2LP_CHECK_MEM_GB` (4 GiB `RLIMIT_AS`). They keep a runaway goal from
taking down the host; the one-off shared-library warm-up compile is exempt
(120 s) so a cold `.lpo` cache can't re-open the parallel write race.
`pp2lp gen` shells out to the vendored Atelier B tools (`krt`,
`vendor/atelierb/<plat>/REPLAY.kin`); you never call them directly.

## Gates

The feedback ladder, fastest first — climb only as far as the change demands:

| gate                                   | time    | catches                                  |
|----------------------------------------|---------|------------------------------------------|
| `cd ocaml && dune build`               | seconds | type/exhaustiveness errors (warn 8 fatal) |
| `cd ocaml && dune runtest`             | seconds | emitter output drift (golden replay→.lp) |
| `./pp2lp audit`                        | seconds | invariants below + both test files       |
| `./pp2lp run og -q`                    | ~3 s    | end-to-end smoke (30 traces)             |
| `./pp2lp run prv -q && pp2lp run claude -q` | ~5 min | full regression (70 + 1207 traces)  |
| apero                                  | n/a     | **not a gate** — the open frontier       |

`pp2lp audit` checks: no `admit` anywhere in `lp/` (no exceptions); no
`trust` token in any emitted `lp/bench` `.lp`; no stray probe files; no
generated parser artifacts in `ocaml/src/`; `bench/test_cli.py` passes
(includes the axiom-inventory check and the OCaml↔Python contract); `dune
runtest` passes.

Pre-commit minimum: `./pp2lp audit && ./pp2lp run og -q`. Run prv + claude
too whenever `ocaml/` or `lp/` (non-bench) changed.

Green counts (updated 2026-06-12): **og 30 ✓, prv 70 ✓, claude 1207 ✓**
(claude checks 1207 of 1284 goals; the rest are gen-time REPLAY drops).

## Invariants

- **Zero admits.** `lp/` contains no `admit` and no postulated oracle. The
  historical `trust` axiom and the 9 unreachable binder-reshape `_1` lemmas
  that used it were removed 2026-06-12; re-adding `trust` for a frontier
  experiment is one line in `B.lp`, but it must not survive a commit.
- **The trusted base is exactly the axiom-inventory allowlist** enforced by
  `bench/test_cli.py`: every bodyless `π`-typed `symbol` in `lp/B.lp` (the
  B-Book set/arithmetic/BOOL primitives), the eight quantifier bridges in
  `lp/Quant.lp` (`pi_to_!!`, `!!_to_pi`, `pi_to_??_intro`, `pi_to_??_elim`,
  and the `♢`/`♡` pairs), and ConjList's `⋀`/`Res` interface. Nothing else.
  A new bodyless symbol anywhere else fails the audit.
- **The engine cannot emit `trust`.** `Lp_tree.term` has no such
  constructor; every solver side-condition, BOOL-membership, AXM-evidence,
  or AR-cancellation that can't be *generated* fails loud with a stable
  `E_*`-coded message instead.
- **Emit dispatch is typed and exhaustive.** Rules carry a `Rule_db.emit`
  variant; the match in `rule_emit.ml`/`translate.ml` is exhaustive with
  warning 8 fatal, so adding a rule *forces* a dispatch arm.

## Mental model

PP is Atelier B's automated first-order prover. A `.but` file (formula +
flags) becomes a `.trace` (postorder), then REPLAY turns that into a
`.replay`: sequent proof nodes prefix-style (rule before child subproofs),
and the result-chain child of a branching quantifier (ALL7/XST8) emitted
*before* the branch rule. Each line carries the per-rule formula annotation
PP saw.

`pp2lp` parses the replay, rebuilds the tree (`proof_tree.ml`), and emits an
`opaque symbol` whose body is a tactic script — each PP rule becomes a
`refine RULE …` against a lemma in `lp/rules/`. Lambdapi type-checks the
symbol. The generated `.lp` has no comments; the engine instead writes a
provenance map (lp line → PP rule, replay line, goal) that the CLI joins
into failure reports.

Three rule shapes, decoded by `Rule_db.strip_suffix` / `is_primed`:

- **base** — `[AND2]`. Plain LP refine in the main sequent proof.
- **`_1` primed** — `[AND2_1]`. Inside a Res-typed equality chain preceding
  a branching quantifier. Chains are emitted as explicit *terms*
  (`refine ALL7 (λ v, …) _`), not tactic blocks — see `translate.ml`'s
  header for why.
- **branching** — ALL7 / XST8: two children, a Res chain plus a
  continuation under the bound variable.

**Binder merging is done at the AST level, not by an LP rule.** PP regroups
adjacent same-quantifier binders — `∀x·∀y·P ↦ ∀(x,y)·P` (spec §A.7–8,
"regroupement des quantifications", plus an *aplatissement* to one flat
tuple) — via merge rules ALL1–4 / XST1–4. `pp2lp` performs that merge in
`Syntax_pp.flatten_binds` (mirroring the aplatissement with `Tuple`'s
`++`/`take`/`drop`), so the goal already carries one compound `Tuple n`
binder and the merge rule is *skipped* (`Rule_db.is_binder_merge`, consumed
at `Translate.tree`). This is **not** a HOAS identity (only ALL6 is) — it is
a deliberate skip: the compound-tuple-encoded merge lemmas put the predicate
at a non-pattern position lambdapi cannot invert. **ALL3 is the exception**:
re-encoded *curried* (`!! w, !! y, P w y` — All.lp) so P is a pattern, and
`branch_cont` emits `refine ALL3 _` for real when a branch continuation's
nested antecedent escapes flattening. The chain (`_1`) forms of the binder
merges are unsupported by design and fail loud at emit; the eventual real
fix is currying the remaining merge rules and deleting `flatten_binds`
(blocked on an inductive tuple-append — see git log around 2026-06-11).

The `Res` encoding (ConjList.lp): a normalisation chain's value is
`Res t` = a snoc list of surviving conjuncts plus a proof `t = conj list`.
`mk_1` wraps single results, `mk_0` discharged (⊤) ones, `concat` merges
lists and erases interior ⊤s. `⋀` is the n-ary conjunction over the same
lists; its four eliminators are part of the trusted base.

## Source layout

```
pp2lp                  the single CLI (Python, one file): run, gen, audit.
ocaml/src/             the engine (each core module has a .mli):
  parse_replay.ml        .replay → rule lines
  rule_db.ml             rule metadata + the typed emit-dispatch key
  proof_tree.ml          rule lines → tree (replay-native state machine)
  translate.ml           tree → lp_tree walker: sequence/assume/branch,
                         main proof vs Res-chain (chain_term)
  rule_emit.ml           per-rule refine construction (exhaustive match)
  emit_ctx.ml            mutable ctx + hyp/witness/INS/ECTR searches
  arith_proofs.ml        generated arithmetic proofs: sum normalisation,
                         cancellation, Farkas combinations (prove_sum_eq,
                         prove_gt_zero, find_arith_contradiction, …)
  syntax_pp.ml           PP AST + flatten_binds + the shared exp traversal
  pp_lp.ml / emit_pp.ml  AST → LP source / AST → PP surface (diagnostics)
  lp_tree.ml / emit_lp.ml  LP term/tactic tree → symbol + header
  errors.ml              `E_*`-coded failwith helper (CLI classifies by prefix)
  free_vars.ml, lexer.mll, parser.mly, reconstruct.ml, bin/main.ml
ocaml/test/            golden tests: replay → .lp diffed against committed
                       expectations (dune runtest; `dune promote` to accept)
lp/
  lambdapi.pkg           package_name = pp2lp
  B.lp                   B-Book primitives — the axiomatic base
  ConjList.lp            ⋀ snoc lists + Res (see Mental model)
  Quant.lp               Tuple n machinery + !! ?? ♢ ♡ and their bridges
  Rules.lp               require-open aggregator for lp/rules/*
  rules/*.lp             per-section rule lemmas (All, Arith, Axm, Bool,
                         Conj, Disj, Eq, Equiv, Impl, Neg, Nrm, Res,
                         TrueFalse, Xst)
  bench/<suite>/<name>/  per-benchmark inputs/artifacts (see Suites)
bench/                 test_cli.py (CLI self-tests + repo contract checks)
                       + results/ (per-run JSON, gitignored)
vendor/atelierb/       vendored REPLAY.kin per platform (used by gen)
vendor/apero/pog/      the CLEARSY POG dataset (gitignored, see Suites)
doc/                   PP spec PDFs (gitignored): pp-spec-full, pp-spec-rules
tex/                   the paper — off limits (see Ground rules)
```

## Workflows

### Debugging a failing trace

Suite results stream live in completion order; failures unfold a **failure
window** — one numbered snippet per related file, headed `filename:position`
with the relevant line marked `>`:

- the **`<name>.probe.lp`** at the error — a persisted, re-checkable copy of
  the emitted `.lp` with `print;` spliced into the failing tactic — followed
  by a prettified **goal state** panel (hypotheses + `⊢ goal`);
- the `.replay` step that produced it;
- the failing rule's `lp/rules/*.lp` signature.

`--lp-debug=CODE` adds `debug +CODE` to that probe run and shows the cleaned
`[tag]` trace (`u`=unification, `r`=rewrite, `t`=tactics, `w`=whnf; bare ⇒
`u`). **Avoid `i`** — type inference crashes lambdapi's printer on our HO
goals. The probe is the only artifact written; re-check it directly to
reproduce.

An emit-side failure prints a stable error code (`E_UNKNOWN_RULE`,
`E_ARITY`, `E_DISPATCH`, `E_TREE_BUILD`, `E_PARSE`, `E_INS`, `E_EMIT`) and a
hint; the engine tags them at the raise site (`Errors.fail`,
`ocaml/src/errors.ml`), and `pp2lp`'s `classify_error` reads the `E_*:`
prefix first, falling back to a message-regex for the parse/tree exception
channel (`Bad_replay`) and old logs. Replay→tree state machine tracing:
`PP2LP_DEBUG_REPLAY=1`.

### Inspecting LP goals / debugging LP rules

Sibling-probe convention: a `lp/rules/Foo_probe.lp` that `require open`s the
module and `print`s/`compute`s the lemma, then `lambdapi check` it. To
inspect a proof mid-state, copy the emitted `NAME.lp` and insert
`print; proofterm;` before a tactic — or use `--lp-debug=u`. **Delete probe
files when done.**

### Adding a corpus goal

1. Add a line to `lp/bench/claude/goals.txt` (`name | kind | goal`) — the
   suite's single source of truth; loose `.but` files get wiped on gen.
   Kinds: `prop`/`expr` self-promote the goal as a hypothesis; `bprop`/
   `bexpr` (bare) make PP genuinely prove it (this is what fires the
   equality-prover rules). `#` existentials are allowed in goals.
2. `pp2lp gen claude` — runs PP/REPLAY; goals PP can't prove or REPLAY
   truncates are dropped loudly.
3. `pp2lp run claude/name`.

### Adding / teaching a new PP rule

1. `ocaml/src/rule_db.ml`: add the rule (arity / phantom / binder_merge /
   hoas_identity) and pick or add an `emit` strategy constructor.
2. The exhaustive match then *forces* dispatch arms in `rule_emit.ml` (or
   `translate.ml` if the rule shapes the tree).
3. The LP lemma goes in the matching `lp/rules/*.lp`; spec recap is
   `doc/pp-spec-rules.pdf` (§8 for rule schemas, §A.7–8 for binder rules).
4. Gate ladder bottom-up; add a golden test if the rule changes emission.

### Apero triage (the open frontier)

apero is huge and **not a clean gate** — work it in families, never
wholesale:

1. `pp2lp run apero --filter '<family>' --json -q` on a bounded subset;
   never iterate over the full suite in a loop.
2. Group failures by the error-code histogram, pick one code/family.
3. Known frontier families are listed under Known broken — check there
   before treating a failure as a regression. A regression is a code
   appearing on a benchmark family that previously passed, or any og/prv/
   claude breakage.
4. `lp/bench/apero/.gen_ledger.json` is the gen pass's content-hash ledger
   (dedupe + resume); never edit it. The dataset lives at
   `PP2LP_APERO_POG` (default `vendor/apero/pog`); `PP2LP_APERO_TIMER`
   (default R45) and `PP2LP_GEN_JOBS` tune the PP pass.

## Suites

- **og** — 30 traces, the baseline smoke test. `.trace`/`.replay` checked in
  (no `.but`; traces are the source of truth). Also the golden-test fixtures.
- **prv** — Atelier B PRV corpus, 70 green. `.but` checked in;
  `.trace`/`.replay` generated.
- **claude** — the synthetic pipeline-stress suite, generated from
  `goals.txt` (source of truth; 1284 goals, 1207 checked — the rest are
  gen-time REPLAY drops). Spans every rule family, proof sizes 1→416 replay
  lines, and probes the failure frontier on purpose; inline notes flag each
  known blocker. `.but` checked in (generation output, kept for diffing).
- **apero** — raw industrial proof obligations from CLEARSY's open POG
  corpus (Zenodo 10.5281/zenodo.7050797: 5434 `.pog` files, 36 projects).
  There is no Atelier B path from `.pog` to PP, so `pp2lp gen apero` renders
  each obligation into PP's own rule-validator input (same `.but` shape as
  prv) and runs PP, fused and streamed: a benchmark dir materialises only
  when PP proves the goal; the ledger makes the pass resumable (`--force`
  resets). The whole suite is gitignored — reproducible from the dataset.

## Known broken / frontiers

- **Chain-nested branching** (`XST8_1 expected a result-chain child but
  stack is empty`) — the largest apero family (~21 of the first 53 complete
  replays) and the same replay-format class as AR7_1/AR8_1 (result-chain
  with no STOP_1 seed). Start: `proof_tree.ml` (the Res-mode stack machine).
- **AR2 over symbolic bounds** — apero side-conditions `a > b` come from
  interval hypotheses, not positive-literal cancellations, so
  `prove_gt_zero` refuses (~16 replays). Start: the in-scope-bound evidence
  route AR5/6 use (`rule_emit.ml`, `emit_ctx.ml`).
- **`FIN_INS(…)` / `__INSTANCIATION(…)` replay lines** — novel INS-evidence
  markers in some apero projects, likely *useful* (they record the witnesses
  the emitter currently searches for). Start: `parse_replay.ml` + the INS
  search in `emit_ctx.ml`.
- **REPLAY losses (upstream).** Detected and dropped at gen as
  `E_REPLAY_TRUNCATED`: the tool omits the final ALL7/XST8 continuation
  (set-extensionality, equality-prover-heavy proofs, literal-constant pins,
  arith-pinned existentials) or writes `**** impossible case in rplMainX ****`
  mid-file. No complete EGALITE replay can currently be produced — that emit
  path is validated against a hand-completed minimal replay.
- **NRM20/21 pin slot ≥ 3** (and NRM26 drops at slot ≥ 3 that aren't
  last-listed): substitution lemmas cover slots 0/1/2 after tail rotation;
  later slots fail loudly. Start: `rule_emit.ml` Nrm20/21 dispatch +
  `lp/rules/Nrm.lp`.
- **BOOL11–52 unreachable end-to-end** — under self-proof they collapse to
  one AXM8; under bare kinds PP can't prove `bool()` round-trips at all (a
  PP limitation). Rule firings overall: 105/138 rule_db names fire; still
  unfired: BOOL*, EAXM2/91/92, EQC1/2, EIMP5*, ECTR5/6, EVR11, NRM16–18,
  NRM27/28/30, ALL2, AR6/7/13, VR2, FX2, XST2/61.

## PP limitations (when authoring goals)

- **BOOL membership**: PP can't reason about `a: BOOL` abstractly; use
  `btrue`/`bfalse` only as concrete terms in equalities.
- **Cascaded `=>`** is left-associative: use `and` for independent
  hypotheses.
- **Set-theoretic surface**: `eql_set`, pair decomposition, and HO set
  operators aren't in the goal-formula syntax.
- **Arithmetic**: AR1–AR13 reduce to `B.lp`'s integer primitives.

## Replay format

```
 [RULE] <formula>          base rule, with per-rule annotation
 [RULE(arg)] <formula>     argument in parens (subscript / hyp / pred)
 [RULE_1] <formula>        primed variant (Res-typed)
 [RULE_N] <formula>        n-ary, binder count N
 [FIN(predicate)] …        phantom (normalisation result)
 [STOP_NORM] / [NRM] …     phantom
```

Main proof is prefix-style; a branching quantifier's result-chain child is
emitted *before* the branch rule. The first non-phantom line's annotation is
the overall goal. `Rule_db.is_phantom` filters phantoms; unknown rule names
raise. PP emits a few `_`-prefixed identifiers (`_eql_set`, `_pj1`, `_pj2`);
the lexer accepts them and the emitter maps them to LP names.

## LP gotchas (repo-specific)

- A bare numeral ≥ 1 in a rewrite-rule *pattern* is a **wildcard**, not the
  literal — spell slot 1 as `+1 0`.
- Never force whnf of a big `int_lit` (decimal numerals exist precisely to
  keep big literals folded).
- `sequential` rule blocks are order-sensitive (the ⊤-erasure rules in
  ConjList must precede the general cons rule).
- Stale `.lpo` after a lambdapi upgrade or lp/ edit storm:
  `find lp -name '*.lpo' -delete`.

## Common errors

| Error                                                  | Where                        | Fix                                                       |
|--------------------------------------------------------|------------------------------|-----------------------------------------------------------|
| `E_UNKNOWN_RULE` (`rule_db: unknown rule "X"`)          | `rule_db.ml`                 | Add `X` to rule_db (arity / phantom / flags).             |
| `E_ARITY` / `E_DISPATCH`                                | `proof_tree.ml`/`translate.ml` | Review the rule's slot kinds / add the dispatch arm.    |
| `E_TREE_BUILD` (`unconsumed rule lines`, `expected a child`) | `proof_tree.ml`         | An earlier rule has the wrong arity; `PP2LP_DEBUG_REPLAY=1`. |
| `E_PARSE`                                               | `parser.mly`/`parse_replay.ml` | Bad replay line; inspect the reported column.           |
| `File X.lpo is incompatible with current binary`        | lambdapi                     | `find lp -name '*.lpo' -delete`.                          |
| `package X cannot be mapped under the library root`     | lambdapi                     | Missing `lambdapi.pkg`; `lp/lambdapi.pkg` covers the package. |
| dune: `file present in source tree` (parser.ml/.conflicts) | menhir promotion          | `rm -f ocaml/src/parser.ml ocaml/src/parser.conflicts`.   |

## Where to start

- New PP rule in a replay → `rule_db.ml` (the exhaustive match forces the
  rest).
- Wrong `refine` arguments → `rule_emit.ml`. Wrong tree structure (sequence/
  assume/branch, main vs chain) → `translate.ml`. Hypothesis / witness / INS
  search → `emit_ctx.ml`. Generated arithmetic proofs → `arith_proofs.ml`.
- LP-side proof gap → `lp/rules/*.lp` + `doc/pp-spec-rules.pdf`.
- Replay format itself → `parse_replay.ml` + `proof_tree.ml`.
- CLI / harness → `./pp2lp` (one Python file) + `bench/test_cli.py`.
