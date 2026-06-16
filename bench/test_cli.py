#!/usr/bin/env python3
"""Self-tests for the pp2lp CLI internals — the pure helpers plus a
contract check that the engine emits a *clean* .lp (no comments) and a
parseable provenance map.

Run from the repo root:  python3 bench/test_cli.py
Exit status is non-zero if any check fails.
"""
import importlib.machinery
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
pp = importlib.machinery.SourceFileLoader("pp2lp_cli", str(ROOT / "pp2lp")).load_module()
pp.COLOR = False                          # deterministic output, no ANSI

_fails = []


def check(name, cond):
    print(f"  {'ok  ' if cond else 'FAIL'}  {name}")
    if not cond:
        _fails.append(name)


def write_tmp(text, suffix):
    tf = tempfile.NamedTemporaryFile("w", suffix=suffix, delete=False, encoding="utf-8")
    tf.write(text)
    tf.close()
    return Path(tf.name)


# ── read_map: parse the engine's provenance TSV ─────────────────────────────
mp = write_tmp("3\tAND1\t1\ta ∧ b\n4\tAXM4\t4\t¬ ¬ p\n", ".provmap")
sm = pp.read_map(mp)
mp.unlink()
check("read_map finds both entries", len(sm) == 2)
check("read_map rules", [e["rule"] for e in sm] == ["AND1", "AXM4"])
check("read_map lp/replay lines", [(e["lp_line"], e["replay_line"]) for e in sm] == [(3, 1), (4, 4)])
check("read_map goal (incl spaces)", sm[1]["goal"] == "¬ ¬ p")

# ── join_prov: nearest preceding ────────────────────────────────────────────
check("join on the exact line", pp.join_prov(4, sm)["rule"] == "AXM4")
check("join between rules → preceding", pp.join_prov(3, sm)["rule"] == "AND1")
check("join above the first → None", pp.join_prov(1, sm) is None)
check("join past the last → last", pp.join_prov(999, sm)["rule"] == "AXM4")

# ── _distill: keep [tag] lines, drop the solve{} dump and crashes ───────────
TRACE = ["debug +u", "[unif] solve {recompute=false;", "       metas={?1:...}",
         "[unif] solve A ≡ B", "[unif] failed", "Start checking foo.lp"]
d = pp._distill(TRACE)
check("distill keeps the constraint", "[unif] solve A ≡ B" in d)
check("distill keeps 'failed'", "[unif] failed" in d)
check("distill drops the solve{} dump", not any("metas" in l or "recompute" in l for l in d))
check("distill drops non-tag noise", not any("Start checking" in l for l in d))
crash = pp._distill(["[infr] Uncaught [...Assertion failed]."])
check("distill surfaces a lambdapi crash", any("internal error" in l for l in crash))

# ── _parse_goal_state: split a probe run into hyps + goal ────────────────────
PROBE_OUT = ['Start checking "x.probe.lp"', "debug +u", "x: P", "hyp: Q",
             "-" * 78, "0. ?4: Q", "[unif] solve P ≡ Q", "[unif] Unsolvable",
             "[/tmp/x.probe.lp:7:0] ", "P", "is not unifiable with", "Q."]
gs = pp._parse_goal_state(PROBE_OUT)
check("goal_state pulls the hypotheses", gs["hyps"] == ["x: P", "hyp: Q"])
check("goal_state strips the N. ?meta: goal prefix", gs["goals"] == ["Q"])
check("goal_state skips the debug echo line", "debug +u" not in gs["hyps"])
check("goal_state stops at the [tag]/[file] lines",
      not any("unif" in h or "unifiable" in h for h in gs["hyps"] + gs["goals"]))
# debug trace still distils from the same output
check("distill coexists with the goal block",
      pp._distill(PROBE_OUT) == ["[unif] solve P ≡ Q", "[unif] Unsolvable"])
empty = pp._parse_goal_state(["nothing here", "no banner"])
check("goal_state empty when no proof banner", empty == {"hyps": [], "goals": []})

# ── _error_headline: drop the re-dumped goal state, flow the rest ────────────
SUBPROOFS = "Missing subproofs (0 subproofs for 3 subgoals):\nx: τ ι\n" + "-" * 78 + "\n0. ?39: τ ι"
check("error_headline keeps only the missing-subproofs head",
      pp._error_headline(SUBPROOFS) == "Missing subproofs (0 subproofs for 3 subgoals):")
check("error_headline flows a wrapped unification error",
      pp._error_headline("A\nis not unifiable with\nB.") == "A is not unifiable with B.")
check("error_headline leaves a colon-free message intact",
      pp._error_headline("  unbound variable foo  ") == "unbound variable foo")

# ── _collapse: fold identical lines into one with a (×N) count ──────────────
col = pp._collapse(["w", "w", "w", "real error", "w"])
check("collapse folds duplicates with a count", col == ["w  (×4)", "real error"])
check("collapse leaves singletons untouched", pp._collapse(["a", "b"]) == ["a", "b"])

# ── _clip ───────────────────────────────────────────────────────────────────
check("clip leaves short strings", pp._clip("abc", 10) == "abc")
check("clip truncates long strings", pp._clip("x" * 20, 10) == "x" * 9 + "…")

# ── classify_error: E_*: prefix wins, regex is the fallback ─────────────────
check("classify reads the E_*: prefix", pp.classify_error("/t.replay: E_DISPATCH: x") == "E_DISPATCH")
check("classify falls back to the regex", pp.classify_error("replay left 3 unconsumed rule lines") == "E_TREE_BUILD")
check("classify defaults to E_EMIT", pp.classify_error("some unrecognised failure") == "E_EMIT")

# ── _failure_histogram: counts per error code over failed goals ─────────────
_goals = [{"status": "ok"},
          {"status": "emit_fail", "error": {"code": "E_DISPATCH"}},
          {"status": "lp_fail", "error": {"code": "E_LP_CHECK"}},
          {"status": "emit_fail", "error": {"code": "E_DISPATCH"}},
          {"status": "warn"}]
_hist = pp._failure_histogram(_goals)
check("histogram counts per code", _hist == {"E_DISPATCH": 2, "E_LP_CHECK": 1})
check("histogram ignores ok/warn goals", sum(_hist.values()) == 3)

# ── _rule_signature: pull a rule's type from lp/rules/ ─────────────────────
# _rule_signature returns (path, start_line, end_line) into lp/rules/*.lp.
sig = pp._rule_signature("NRM14")
check("rule_signature finds NRM14",
      sig is not None and sig[0].suffix == ".lp"
      and "symbol NRM14" in sig[0].read_text().splitlines()[sig[1] - 1])
check("rule_signature strips a leading @", pp._rule_signature("@AR10") == pp._rule_signature("AR10"))

# ── contract: the engine emits a CLEAN .lp + a parseable map ────────────────
eng = ROOT / "ocaml" / "_build" / "default" / "bin" / "main.exe"
rep = ROOT / "lp" / "bench" / "og" / "01" / "01.replay"
if eng.exists() and rep.exists():
    mapfile = write_tmp("", ".provmap")
    r = subprocess.run([str(eng), "emit", "--map", str(mapfile), str(rep)],
                       cwd=ROOT, capture_output=True, text=True)
    m = pp.read_map(mapfile)
    mapfile.unlink()
    check("engine emits a clean .lp (no /* comments)", "/*" not in r.stdout)
    check("engine map is parseable (OCaml↔Python contract)",
          len(m) >= 5 and all(e["rule"] and e["replay_line"] > 0 for e in m))
else:
    print("  skip  engine contract test (build the engine first)")

# ── contract: a failure carries a stable E_*: prefix the CLI classifies ──────
if eng.exists():
    bad = write_tmp("[BOGUSRULE] <a => b>\n", ".replay")
    r = subprocess.run([str(eng), "emit", "--map", "/dev/null", str(bad)],
                       cwd=ROOT, capture_output=True, text=True)
    bad.unlink()
    check("unknown rule → E_UNKNOWN_RULE: prefix on stderr",
          r.returncode != 0 and "E_UNKNOWN_RULE:" in r.stderr)
    check("classify_error reads the prefix (engine↔CLI contract)",
          pp.classify_error(r.stderr) == "E_UNKNOWN_RULE")
else:
    print("  skip  E_* prefix contract (build the engine first)")

# ── resolver: suite enumeration (powers the "available: …" recovery hint) ────
suites = pp._suite_names()
check("suite_names lists og + claude", "og" in suites and "claude" in suites)
check("suite_names skips dotfiles/__pycache__", not any(s.startswith((".", "_")) for s in suites))

print(f"\n{'ALL PASS' if not _fails else f'{len(_fails)} FAILED'}")
sys.exit(1 if _fails else 0)
