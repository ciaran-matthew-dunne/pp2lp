#!/usr/bin/env python3
"""Self-tests for the pp2lp CLI internals — the pure helpers plus a
contract check that the engine emits a *clean* .lp (no comments) and a
parseable provenance map.

Run from the repo root:  python3 bench/test_cli.py
Exit status is non-zero if any check fails.
"""
import contextlib
import importlib.machinery
import io
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


def capture(fn, *args):
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        fn(*args)
    return buf.getvalue()


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
d = pp._distill(TRACE, raw_mode=False)
check("distill keeps the constraint", "[unif] solve A ≡ B" in d)
check("distill keeps 'failed'", "[unif] failed" in d)
check("distill drops the solve{} dump", not any("metas" in l or "recompute" in l for l in d))
check("distill drops non-tag noise", not any("Start checking" in l for l in d))
crash = pp._distill(["[infr] Uncaught [...Assertion failed]."], raw_mode=False)
check("distill surfaces a lambdapi crash", any("internal error" in l for l in crash))

# ── _clip ───────────────────────────────────────────────────────────────────
check("clip leaves short strings", pp._clip("abc", 10) == "abc")
check("clip truncates long strings", pp._clip("x" * 20, 10) == "x" * 9 + "…")

# ── _print_lp_goals: panel shows GOALS, not just hypotheses ─────────────────
MSG = ["Missing subproofs (0 for 2):", "h1: T", "h2: T", "-" * 40, "0. ?1 : A", "1. ?2 : B"]
out = capture(pp._print_lp_goals, MSG, "")
check("panel shows the goals", "0. ?1 : A" in out and "1. ?2 : B" in out)
check("panel summarizes hypotheses", "2 hypotheses" in out)
check("panel does not spew raw hyp lines", "h1: T" not in out)

# ── _rule_signature: pull a rule's type from lp/rules/ ─────────────────────
sig = pp._rule_signature("NRM14")
check("rule_signature finds NRM14", sig is not None and "symbol NRM14" in sig[1] and sig[0].endswith(".lp"))
check("rule_signature strips a leading @", pp._rule_signature("@AR10") == pp._rule_signature("AR10"))

# ── contract: the engine emits a CLEAN .lp + a parseable map ────────────────
eng = ROOT / "ocaml" / "_build" / "default" / "bin" / "main.exe"
rep = ROOT / "lp" / "bench" / "og" / "01.replay"
if eng.exists() and rep.exists():
    mapfile = write_tmp("", ".provmap")
    r = subprocess.run([str(eng), "emit", "--map", str(mapfile), "lp/bench/og/01.replay"],
                       cwd=ROOT, capture_output=True, text=True)
    m = pp.read_map(mapfile)
    mapfile.unlink()
    check("engine emits a clean .lp (no /* comments)", "/*" not in r.stdout)
    check("engine map is parseable (OCaml↔Python contract)",
          len(m) >= 5 and all(e["rule"] and e["replay_line"] > 0 for e in m))
else:
    print("  skip  engine contract test (build the engine first)")

print(f"\n{'ALL PASS' if not _fails else f'{len(_fails)} FAILED'}")
sys.exit(1 if _fails else 0)
