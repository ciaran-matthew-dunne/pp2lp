#!/usr/bin/env python3
"""Format lambdapi --json (NDJSON) output for make check.

Reads lambdapi --json stdout from stdin. Emits a concise error report:
location, message, and (optionally) deduplicated emitter warnings.

Falls back to ANSI-stripped grep for lambdapi builds that predate --json.

Usage:
  lambdapi check --json file.lp >lp.out 2>&1
  python3 format_error.py [warnings] < lp.out
"""
import sys, json, os, re
from collections import Counter

warnings_text = sys.argv[1] if len(sys.argv) > 1 else ""
project_root = os.environ.get("PP2LP_ROOT", "")


def rel(path):
    if project_root and isinstance(path, str) and path.startswith(project_root):
        return path[len(project_root):].lstrip("/")
    return path


raw = sys.stdin.read()

errors = []
for line in raw.splitlines():
    line = line.strip()
    if not line.startswith("{"):
        continue
    try:
        rec = json.loads(line)
    except (json.JSONDecodeError, ValueError):
        continue
    if rec.get("kind") == "diagnostic" and rec.get("severity") == "error":
        errors.append(rec)

if errors:
    for rec in errors:
        f = rel(rec.get("file") or "?")
        start = (rec.get("range") or {}).get("start") or {}
        loc = f"{f}:{start.get('line')}:{start.get('col')}" if start else f
        print(f"  {loc}")
        msg = rec.get("message", "?")
        for i, ln in enumerate(msg.split("\n")):
            prefix = "  error: " if i == 0 else "         "
            print(f"{prefix}{ln}")
else:
    text = re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", raw)
    err_lines = [ln for ln in text.splitlines()
                 if re.search(r"\b(error|Error|Cannot|Unknown)\b", ln)]
    for ln in (err_lines or text.splitlines())[-5:]:
        print(f"  {ln}")

if warnings_text.strip():
    counts = Counter(warnings_text.strip().split("\n"))
    print("  warnings:")
    for w, n in counts.items():
        print(f"    {w}" + (f" (x{n})" if n > 1 else ""))
