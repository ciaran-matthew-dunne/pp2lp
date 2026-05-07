#!/usr/bin/env python3
"""Format `lambdapi check --json` output for terminal use."""

import json
import sys
import argparse
from pathlib import Path


def iter_lines(paths):
    if not paths:
        yield from sys.stdin
        return
    for path in paths:
        with open(path, encoding="utf-8") as handle:
            yield from handle


def rel(path):
    try:
        return str(Path(path).resolve().relative_to(Path.cwd()))
    except Exception:
        return path


def loc_of(event):
    path = rel(event.get("file", "?"))
    range_ = event.get("range") or {}
    start = range_.get("start") or {}
    end = range_.get("end") or {}
    line = start.get("line")
    col = start.get("col")
    end_line = end.get("line")
    end_col = end.get("col")
    if line is None or col is None:
        return path
    if end_line is None or end_col is None:
        return f"{path}:{line}:{col}"
    return f"{path}:{line}:{col}-{end_line}:{end_col}"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--ok", action="store_true",
                        help="print OK if the input contains no structured summary")
    parser.add_argument("paths", nargs="*")
    args = parser.parse_args()

    diagnostics = []
    summaries = []
    file_ends = []
    raw = []

    for line in iter_lines(args.paths):
        line = line.rstrip("\n")
        if not line:
            continue
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            raw.append(line)
            continue
        kind = event.get("kind")
        if kind == "diagnostic":
            diagnostics.append(event)
        elif kind == "summary":
            summaries.append(event)
        elif kind == "file_end":
            file_ends.append(event)

    has_error = False
    for event in diagnostics:
        severity = event.get("severity", "diagnostic")
        if severity != "warning":
            has_error = True
        message = event.get("message", "").rstrip()
        lines = message.splitlines() if message else [""]
        print(f"{loc_of(event)}: {severity}: {lines[0]}")
        for extra in lines[1:]:
            print(f"  {extra}")

    if has_error:
        return

    for line in raw:
        print(line)

    if summaries:
        summary = summaries[-1]
        checked = summary.get("files_checked", 0)
        ok = summary.get("files_ok", 0)
        failed = summary.get("files_failed", 0)
        elapsed = summary.get("elapsed_ms")
        suffix = f" ({elapsed}ms)" if elapsed is not None else ""
        print(f"OK {ok}/{checked} files, {failed} failed{suffix}")
    elif file_ends:
        event = file_ends[-1]
        elapsed = event.get("elapsed_ms")
        suffix = f" ({elapsed}ms)" if elapsed is not None else ""
        print(f"{event.get('status', 'done').upper()} {rel(event.get('file', '?'))}{suffix}")
    elif args.ok:
        print("OK")


if __name__ == "__main__":
    main()
