#!/usr/bin/env python3
"""Generate results-data.tex from the benchmark JSON — single source of truth.

The paper's numbers live in lp/bench/results/<suite>.json (emit) and
<suite>.check.json (check), written by `pp2lp run` / `pp2lp check`.  Rather
than hand-editing macros, regenerate results-data.tex after a suite run:

    python3 paper/results-data.py        # from tex/, or anywhere

results-data.tex stays committed so the paper builds without the (gitignored,
multi-megabyte) JSON; this script only rewrites it when the JSON is present.
Per suite we report, from the two JSON files,

    Replays   = emit ok + emit fail            (benchmarks PP/REPLAY produced)
    Verified  = check ok
    Timeouts  = emit E_TIMEOUT + check E_LP_TIMEOUT   (budget, not a failure)
    Failures  = Replays - Verified - Timeouts        (genuine emit/check fails)

so Verified + Timeouts + Failures = Replays by construction.
"""
import json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
RES  = os.path.join(ROOT, "lp", "bench", "results")
SUITES = ["og", "prv", "claude", "apero"]

# ── manually-maintained constants (not derivable from the JSON) ──────────
MANUAL = {
    "numRulesSpec":    "140",                     # PP spec Annexe A (approx.)
    "numRulesCovered": "138",                     # rule_db.ml entries
    "aperoMedianHyps": r"1\,700",                 # median hypothesis count (approx.)
    "benchMachine":    "a 32-thread Intel i9 laptop",
    "benchWallAll":    "about half a minute",     # og+prv+claude, emit+check wall
    "benchCpuAll":     "about ten CPU-minutes",   # og+prv+claude, check CPU
}

def load(name):
    with open(os.path.join(RES, name)) as f:
        return json.load(f)

def suite_metrics(s):
    e, c = load(f"{s}.json"), load(f"{s}.check.json")
    eb, cb = e.get("by_code") or {}, c.get("by_code") or {}
    replays  = e["ok"] + e["fail"]
    verified = c["ok"]
    timeouts = eb.get("E_TIMEOUT", 0) + cb.get("E_LP_TIMEOUT", 0)
    failures = replays - verified - timeouts
    if failures < 0:
        sys.exit(f"{s}: negative failure count ({replays=} {verified=} {timeouts=})")
    return dict(Replayed=replays, Pass=verified, Timeout=timeouts, Failed=failures)

def count_lines(paths):
    n = 0
    for p in paths:
        with open(p, errors="ignore") as f:
            n += sum(1 for _ in f)
    return n

def walk(base, suffixes, prune=()):
    out = []
    for d, _, files in os.walk(base):
        if any(os.path.abspath(d).startswith(os.path.abspath(p)) for p in prune):
            continue
        out += [os.path.join(d, f) for f in files if f.endswith(suffixes)]
    return out

def rules_fired():
    """rule_db base-names that fire in some replay (FOO_1 -> FOO)."""
    markers = {"NRM", "FIN", "STOP_NORM"}
    db = re.findall(r'\br\s+"([A-Z][A-Z0-9_]+)"',
                    open(os.path.join(ROOT, "ocaml/src/rule_db.ml")).read())
    base = lambda t: re.sub(r'(_\d+)+$', "", t)
    dbbase = {base(n) for n in db if n not in markers}
    fired = set()
    for s in SUITES:
        for f in walk(os.path.join(ROOT, "lp/bench", s), (".replay",)):
            for m in re.findall(r'\[([A-Z][A-Za-z0-9_]+?)(?:\([^)]*\))?\]',
                                open(f, errors="ignore").read()):
                if m not in markers:
                    fired.add(base(m))
    return len(dbbase & fired)

def main():
    missing = [n for s in SUITES for n in (f"{s}.json", f"{s}.check.json")
               if not os.path.exists(os.path.join(RES, n))]
    if missing:
        # No (gitignored) JSON here — keep the committed results-data.tex so the
        # paper still builds.  Exit 0 so this is a safe no-op inside `make`.
        print("results-data.py: no benchmark JSON, keeping committed "
              "results-data.tex (missing " + ", ".join(missing) + ")",
              file=sys.stderr)
        return

    m = {s: suite_metrics(s) for s in SUITES}
    agg = lambda key, suites: sum(m[s][key] for s in suites)
    macros = {}
    for s in SUITES:
        for k, v in m[s].items():
            macros[f"{s}{k}"] = v
    ctrl = ["og", "prv", "claude"]
    macros["ctrlReplayed"], macros["ctrlPass"] = agg("Replayed", ctrl), agg("Pass", ctrl)
    for k in ("Replayed", "Pass", "Timeout", "Failed"):
        macros[f"all{k}"] = agg(k, SUITES)

    # LoC is an "about N" prose figure: round to the nearest 100 so ongoing
    # source edits do not churn the committed file.
    r100 = lambda n: int(round(n / 100.0)) * 100
    macros["toolOcamlLines"] = r100(count_lines(
        walk(os.path.join(ROOT, "ocaml/src"), (".ml", ".mli", ".mll", ".mly"))))
    macros["toolLpLines"] = r100(count_lines(
        walk(os.path.join(ROOT, "lp"), (".lp",), prune=[os.path.join(ROOT, "lp/bench")])))
    macros["prvGoals"] = len(walk(os.path.join(ROOT, "lp/bench/prv"), (".but",)))
    macros["numRulesFired"] = rules_fired()

    lines = [
        "% ════════════════════════════════════════════════════════════════════",
        "%  AUTO-GENERATED by paper/results-data.py — DO NOT EDIT BY HAND.",
        "%  Refresh after a suite run:  python3 paper/results-data.py",
        "%  Volatile counts come from lp/bench/results/*.json; the few constants",
        "%  not in the JSON (rule totals, median hyps, machine, timing) are the",
        "%  MANUAL dict at the top of that script.",
        "% ════════════════════════════════════════════════════════════════════",
        "",
        "% ---- per-suite (Replays / Verified / Timeouts / Failures) ----------",
    ]
    for s in SUITES:
        lines.append("".join(
            f"\\newcommand{{\\{s}{k}}}{{{m[s][k]}}}" for k in ("Replayed", "Pass", "Timeout", "Failed")))
    lines += [
        "",
        "% ---- aggregates ----------------------------------------------------",
        f"\\newcommand{{\\ctrlReplayed}}{{{macros['ctrlReplayed']}}}"
        f"\\newcommand{{\\ctrlPass}}{{{macros['ctrlPass']}}}"
        "  % og+prv+claude (controlled suites)",
        "".join(f"\\newcommand{{\\all{k}}}{{{macros['all'+k]}}}"
                for k in ("Replayed", "Pass", "Timeout", "Failed")),
        "",
        "% ---- derived from the tree (lines of code, goal counts) ------------",
        f"\\newcommand{{\\toolOcamlLines}}{{{macros['toolOcamlLines']}}}"
        f"\\newcommand{{\\toolLpLines}}{{{macros['toolLpLines']}}}",
        f"\\newcommand{{\\prvGoals}}{{{macros['prvGoals']}}}"
        f"\\newcommand{{\\numRulesFired}}{{{macros['numRulesFired']}}}",
        "",
        "% ---- manual constants (see MANUAL in results-data.py) --------------",
    ]
    for k, v in MANUAL.items():
        lines.append(f"\\newcommand{{\\{k}}}{{{v}}}")
    lines.append("")

    out = os.path.join(HERE, "results-data.tex")
    with open(out, "w") as f:
        f.write("\n".join(lines))
    print("wrote", os.path.relpath(out, ROOT))
    for s in SUITES:
        print(f"  {s:7}", m[s])
    print(f"  fired {macros['numRulesFired']}/{MANUAL['numRulesCovered']} rules, "
          f"ocaml {macros['toolOcamlLines']}, lp {macros['toolLpLines']}")

if __name__ == "__main__":
    main()
