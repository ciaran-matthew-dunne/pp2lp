#!/usr/bin/env python3
"""Format lambdapi JSON error output for make check.

Reads lambdapi --json output from stdin. Accepts emitter warnings as an
optional CLI argument. Designed for tight agent feedback loops: shows
location, error, proof state, and deduplicated warnings concisely.

Usage:
  lambdapi check --json file.lp 2>&1 | python3 format_error.py [warnings]
"""
import sys, json, os, re
from collections import Counter

# ── Parse args ───────────────────────────────────────────────────────────────
warnings_text = sys.argv[1] if len(sys.argv) > 1 else ""
project_root = os.environ.get("PP2LP_ROOT", "")

raw = sys.stdin.read()
try:
    d = json.loads(raw)
except (json.JSONDecodeError, ValueError):
    # Non-JSON output (lambdapi without --json): strip ANSI, show error lines.
    text = re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", raw)
    err_lines = [ln for ln in text.splitlines()
                 if re.search(r"\b(error|Error|Cannot|Unknown)\b", ln)]
    for ln in (err_lines or text.splitlines())[-5:]:
        print(f"  {ln}")
    sys.exit(0)

f = d.get("file") or "?"
ln = d.get("start_line")
col = d.get("start_col")
msg = d.get("message", "?")

# Shorten absolute path to relative
if project_root and isinstance(f, str) and f.startswith(project_root):
    f = f[len(project_root):].lstrip("/")

# ── Location + error ────────────────────────────────────────────────────────
loc = f"{f}:{ln}:{col}" if ln is not None else f
print(f"  {loc}")
for i, line in enumerate(msg.split("\n")):
    prefix = "  error: " if i == 0 else "         "
    print(f"{prefix}{line}")

# ── Proof state ──────────────────────────────────────────────────────────────
ps = d.get("proof_state")
if ps and isinstance(ps, dict):
    goals = ps.get("goals", [])
    for gi, g in enumerate(goals):
        gid = g.get("id", "?")
        hyps = g.get("hyps", [])
        # Split hypotheses: proof-relevant (π ...) vs domain variables (τ ι)
        proof_hyps = []
        domain_vars = []
        for h in hyps:
            ty = h.get("type", "")
            if ty.lstrip(": ").startswith("π"):
                proof_hyps.append(h)
            else:
                domain_vars.append(h)

        print(f"  goal {gid}:")
        if domain_vars:
            names = " ".join(h["name"] for h in domain_vars)
            print(f"    vars: {names}")
        for h in proof_hyps:
            print(f"    {h['name']} {h['type']}")
        ty = g.get("type", "")
        print(f"    ⊢ {ty}")

# ── Emitter warnings (deduplicated) ─────────────────────────────────────────
if warnings_text.strip():
    counts = Counter(warnings_text.strip().split("\n"))
    if counts:
        print("  warnings:")
        for w, n in counts.items():
            if n > 1:
                print(f"    {w} (x{n})")
            else:
                print(f"    {w}")
