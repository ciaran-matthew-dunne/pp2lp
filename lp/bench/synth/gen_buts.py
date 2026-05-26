#!/usr/bin/env python3
"""Generate synthetic PP .but files from goals.txt."""

from __future__ import annotations

import re
from pathlib import Path


HERE = Path(__file__).resolve().parent
GOALS = HERE / "goals.txt"
IDENT_RE = re.compile(r"\b[a-z][A-Za-z0-9_]*\b")
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


def parse_goals() -> list[tuple[str, str, str]]:
    goals: list[tuple[str, str, str]] = []
    for lineno, raw in enumerate(GOALS.read_text().splitlines(), start=1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        fields = [field.strip() for field in line.split("|", 2)]
        if len(fields) != 3:
            raise SystemExit(f"{GOALS}:{lineno}: expected 'name | kind | goal'")
        name, kind, goal = fields
        if not re.fullmatch(r"[a-z][a-z0-9_]*", name):
            raise SystemExit(f"{GOALS}:{lineno}: invalid goal name {name!r}")
        if kind not in {"prop", "expr"}:
            raise SystemExit(f"{GOALS}:{lineno}: kind must be prop or expr")
        if not goal:
            raise SystemExit(f"{GOALS}:{lineno}: empty goal")
        goals.append((name, kind, goal))
    return goals


def identifiers(goal: str) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for ident in IDENT_RE.findall(goal):
        if ident in KEYWORDS or ident in seen:
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
    goals = parse_goals()
    for path in HERE.glob("*.but"):
        path.unlink()
    for name, kind, goal in goals:
        (HERE / f"{name}.but").write_text(but_content(name, kind, goal))
    print(f"generated {len(goals)} .but files under {HERE.relative_to(HERE.parent.parent)}")


if __name__ == "__main__":
    main()
