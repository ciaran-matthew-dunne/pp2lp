#!/usr/bin/env python3
"""Report the paper's BODY page count (excludes appendices and bibliography).

The LPAR-26 limit (8 pages) is on the body only.  We take the body to end on
the page before the first appendix section, i.e.

    body = min(page of any 'app:*' \\newlabel) - 1.

Run after a build, so pp2lp.aux is fresh.  Exits non-zero when over budget, so
a loop can branch on the status:  python3 bodypages.py && echo fits.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
AUX = os.path.join(HERE, "pp2lp.aux")
LIMIT = 8

try:
    aux = open(AUX).read()
except FileNotFoundError:
    sys.exit(f"bodypages: {AUX} not found — build the paper first")

pages = [int(p) for _, p in
         re.findall(r"\\newlabel\{(app:[^}]+)\}\{\{[^}]*\}\{(\d+)\}", aux)]
if not pages:
    sys.exit("bodypages: no 'app:*' label in the .aux — appendix missing, or "
             "the first appendix \\section lacks an app: label")

body = min(pages) - 1
over = body - LIMIT
status = "OK — within budget" if over <= 0 else f"OVER budget by {over} page(s)"
print(f"body = {body} pages (limit {LIMIT}) — {status}")
sys.exit(0 if over <= 0 else 1)
