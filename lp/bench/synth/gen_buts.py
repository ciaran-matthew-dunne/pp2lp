#!/usr/bin/env python3
"""Generate synthetic PP .but files from a suite's goals.txt.

Defaults to the `synth` suite (this file's own directory).  Pass
`--suite nrm_test` (etc.) to drive any other `lp/bench/<suite>/goals.txt`
— the nrm_test suite reuses this generator for NRM-rule coverage goals."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


HERE = Path(__file__).resolve().parent
BENCH = HERE.parent  # lp/bench
IDENT_RE = re.compile(r"\b[a-z][A-Za-z0-9_]*\b")
# Bound-variable groups: the var(s) between a `!`/`#` binder and its `.`.
BINDER_RE = re.compile(r"[!#]\s*\(?\s*([a-zA-Z0-9_,\s]+?)\s*\)?\s*\.")
KEYWORDS = {
    "BOOL",
    "FALSE",
    "INTEGER",
    "NAT",
    "NATURAL",
    "NATURAL1",
    "POW",
    "TRUE",
    "bool",
    "card",
    "dom",
    "false",
    "id",
    "not",
    "or",
    "ran",
    "true",
}


def parse_goals(goals_path: Path) -> list[tuple[str, str, str, bool]]:
    goals: list[tuple[str, str, str, bool]] = []
    for lineno, raw in enumerate(goals_path.read_text().splitlines(), start=1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        # `name | kind | goal` with an optional 4th `xfail` field that routes
        # the goal to the xfail/ subdir (excluded from the bulk suite run).
        # Goals must not themselves contain `|`.
        fields = [field.strip() for field in line.split("|")]
        if len(fields) not in (3, 4):
            raise SystemExit(
                f"{goals_path}:{lineno}: expected 'name | kind | goal [| xfail]'")
        name, kind, goal = fields[0], fields[1], fields[2]
        xfail = len(fields) == 4
        if xfail and fields[3] != "xfail":
            raise SystemExit(
                f"{goals_path}:{lineno}: 4th field must be 'xfail', got {fields[3]!r}")
        if not re.fullmatch(r"[a-z][a-z0-9_]*", name):
            raise SystemExit(f"{goals_path}:{lineno}: invalid goal name {name!r}")
        if kind not in {"prop", "expr"}:
            raise SystemExit(f"{goals_path}:{lineno}: kind must be prop or expr")
        if not goal:
            raise SystemExit(f"{goals_path}:{lineno}: empty goal")
        goals.append((name, kind, goal, xfail))
    return goals


def bound_identifiers(goal: str) -> set[str]:
    """Variables bound by an explicit quantifier (`!x.`, `#x.`, `!(x,y).`).
    PP emits delta hypotheses only for the *free* identifiers, so bound
    variables must be excluded — otherwise a goal like `!x.(x: u => ...)`
    would get a bogus `_delta_e(x)`."""
    out: set[str] = set()
    for match in BINDER_RE.finditer(goal):
        for var in match.group(1).split(","):
            var = var.strip()
            if var:
                out.add(var)
    return out


def identifiers(goal: str) -> list[str]:
    bound = bound_identifiers(goal)
    seen: set[str] = set()
    out: list[str] = []
    for ident in IDENT_RE.findall(goal):
        if ident in KEYWORDS or ident in bound or ident in seen:
            continue
        seen.add(ident)
        out.append(ident)
    return out


def delta_hyps(kind: str, goal: str) -> str:
    prefix = "_delta_p" if kind == "prop" else "_delta_e"
    return " & ".join(f"{prefix}({ident})" for ident in identifiers(goal))


def but_content(name: str, kind: str, goal: str) -> str:
    deltas = delta_hyps(kind, goal)
    hypotheses = f"({goal})"
    if deltas:
        hypotheses = f"{hypotheses} & {deltas}"
    return (
        f'Flag(FileOn("{name}.res")) & '
        f"Set(Valid.1 | Rule(Implication | {hypotheses} | ? | ? | {goal} | nn))\n"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--suite", default="synth",
                        help="suite under lp/bench/ (default: synth)")
    args = parser.parse_args()
    work = (HERE if args.suite == "synth" else BENCH / args.suite)
    goals_path = work / "goals.txt"
    if not goals_path.exists():
        raise SystemExit(f"no goals.txt for suite {args.suite!r} ({goals_path})")

    goals = parse_goals(goals_path)
    xfail_dir = work / "xfail"
    for path in work.glob("*.but"):
        path.unlink()
    for path in xfail_dir.glob("*.but"):
        path.unlink()
    n_main = n_xfail = 0
    for name, kind, goal, xfail in goals:
        out_dir = xfail_dir if xfail else work
        out_dir.mkdir(parents=True, exist_ok=True)
        (out_dir / f"{name}.but").write_text(but_content(name, kind, goal))
        if xfail:
            n_xfail += 1
        else:
            n_main += 1
    rel = work.relative_to(BENCH.parent.parent)
    suffix = f" (+{n_xfail} in {rel}/xfail/)" if n_xfail else ""
    print(f"generated {n_main} .but files under {rel}{suffix}")


if __name__ == "__main__":
    main()
