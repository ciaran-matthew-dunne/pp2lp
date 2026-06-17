#!/usr/bin/env python3
"""Self-tests for the pp2lp CLI internals — the pure helpers plus a
contract check that the engine emits a *clean* .lp (no comments) and a
parseable provenance map.

Run from the repo root:  python3 lp/bench/test_cli.py
Exit status is non-zero if any check fails.
"""
import importlib.machinery
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]   # lp/bench/test_cli.py → repo root
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

# ── _goal_state_for: adapt lambdapi's structured goals to {hyps, goals} ──────
# goals_after (subproof mismatch) wins over goals_before; each goal carries hyps.
DIAG = {"goals_before": [{"hyps": [{"name": "x", "type": "P"}], "concl": "Q"}],
        "goals_after": [{"hyps": [{"name": "h", "type": "A"}], "concl": "B"},
                        {"hyps": [], "constr": "C ≡ D"}]}
gsf = pp._goal_state_for(DIAG)
check("goal_state_for prefers goals_after", gsf["goals"] == ["B", "C ≡ D"])
check("goal_state_for takes the focused goal's hyps", gsf["hyps"] == ["h : A"])
check("goal_state_for falls back to goals_before",
      pp._goal_state_for({"goals_before": DIAG["goals_before"]})["goals"] == ["Q"])
check("goal_state_for empty when the diagnostic carries no goals",
      pp._goal_state_for({}) == {"hyps": [], "goals": []})

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

# ── _Stream._matches: the --code failure-window filter ──────────────────────
_s_ins = pp._Stream("apero", 3, code_rx=re.compile("E_INS", re.I))
check("code filter keeps the matching code",
      _s_ins._matches({"status": "emit_fail", "error": {"code": "E_INS"}}))
check("code filter drops a non-matching code",
      not _s_ins._matches({"status": "emit_fail", "error": {"code": "E_TREE_BUILD"}}))
check("no code filter keeps every failure",
      pp._Stream("apero", 1)._matches({"status": "emit_fail", "error": {"code": "E_X"}}))

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
