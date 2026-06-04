# nrm_test — NRM rule coverage

This suite deliberately exercises PP's normalisation rules (`NRM*`, spec
§8.13–8.16).  Goals are PP-provable surface forms (set/relation expressions);
each is proved from itself + `_delta` hypotheses, and **promoting the
goal-as-hypothesis** drives ALL7 normalisation, firing NRM rules on the body's
structure.  `goals.txt` is the source of truth, fed to the shared generator
via `pp2lp gen nrm_test` (same path as synth).

Regenerate + check:

```
pp2lp gen nrm_test    # (re)build .but/.trace/.replay (PP/REPLAY via krt)
pp2lp run nrm_test    # emit + check; strict gate (child-process capped)
```

Coverage is measured emit-side with the engine's `rules` command
(`ocaml/_build/default/bin/main.exe rules <replay>`) — never loop raw
`lambdapi check`, which has no memory cap and the `x: NAT` goals OOM the host.

## Status (20 / 26 implemented rules triggered)

`✓` a goal triggering it type-checks · `✗` triggered but doesn't type-check yet
· `—` no goal triggers it here.

| Rule | Status | Representative goal | Note |
|------|--------|---------------------|------|
| NRM1  | ✓ | `s <: s` | vacuous quantifier |
| NRM2  | ✓ | `!x.(a: t => x: s)` | x-free antecedent |
| NRM3  | ✓ | `{x} <: s` | x not free in consequent |
| NRM4  | ✓ | `!x.(x: s => a: t => b: u => x: v)` | x-free middle (single middle → NRM2) |
| NRM5  | ✓ | `f: s +-> t` | `∧`-antecedent / cascade |
| NRM6  | ✓ | `s <: t /\ u` | `∧`-consequent split |
| NRM7  | ✓ | `!x.(x: a => x: b => x: c)` | bare `∧` split |
| NRM8  | ✓ | `x: dom(f) & f(x) = y` | compound binder |
| NRM9  | ✗ | `s <: POW(t)` | `res_tm` chain |
| NRM10 | ✗ | `f: s --> t` | functional-uniqueness `res_tm` chain |
| NRM11 | — | — | needs literal `P ⇒ FALSE` body (self-proof yields `¬P` → NRM12/14) |
| NRM12 | ✓ | `!x.(x: s => not(x: t))` | `P ⇒ ¬Q` |
| NRM13 | ✓ | `!x.(x: u => x: a & x: b & x: c)` | (fires almost everywhere) |
| NRM14 | ✓ | `!x.not(x: s)` | `¬P` |
| NRM15 | ✓ | `!x.(a: t => x: s)` | `¬¬P` |
| NRM16 | — | — | needs `∀x·P` already in H (contradiction discovery, §8.16) |
| NRM17 | — | — | contradiction on promotion — needs two interacting universals |
| NRM18 | — | — | contradiction on promotion — needs two interacting universals |
| NRM19 | ✓ | `x: dom(f)` | witness instantiation |
| NRM20 | ✗ | `{a}*b <: c` | NRM20 proven; fails on surrounding `res_tm` chain |
| NRM21 | ✗ | `!(x,y).(a = x & y: b => x,y: c)` | reversed `E = x`; emit unverified |
| NRM22 | ✓ | `{x} <: s` | `x = E` substitution (literal-⊤) |
| NRM23 | ✗ | `!x.(a = x => x: s)` | reversed `E = x`; emit unverified |
| NRM24 | — | — | TRUE-strip optimisation; PP keeps `¬(⊤ ∧ P)` instead |
| NRM25 | — | — | vacuous `♡`-binder intro (self-proof drops it via NRM1) |
| NRM26 | ✗ | `!x.!y.(x: s => y: t => x: s)` | binder extension; `res_tm` chain |
| NRM27–30 | — | — | arithmetic solver; not in `rule_db` (not-impl). `x: NAT` goals run but OOM (RLIMIT_AS-capped). |

## Not yet triggered — why

- **NRM11, 24, 25** — structural variants the self-proving harness normalises
  *past* (e.g. `¬P` is emitted directly rather than `P ⇒ FALSE`; a vacuous
  binder is dropped by NRM1 before NRM25 can fire).
- **NRM16, 17, 18** — §8.16 "contradiction on hypothesis promotion": they need
  two *interacting* universal hypotheses (one in H, one being promoted). The
  generator only puts the goal itself in H, so no contradiction arises.
  Triggering these would need a `goals.txt` extension for custom hypotheses.
- **NRM27–30** — arithmetic-solver normalisation; not implemented in `rule_db`
  and not reached by the `≤`/`NAT` goals tried.

## Failing rows

The `✗` rows above fail `lambdapi check` for reasons *separate* from the NRM
rule under test — chiefly the ConjList/Res `res_tm STOP_1` incompleteness shared
with synth, and the unverified NRM21/23 emit. The gate is strict (no baseline):
these count as real failures until the underlying rule support lands.
