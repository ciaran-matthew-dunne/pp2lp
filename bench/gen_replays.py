#!/usr/bin/env python3
"""Generate optional PP `.replay` files from existing `.trace` files.

Replays are debugging artifacts only. The OCaml pp2lp tool reads traces
directly and does not consume these files.
"""

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path


FAILURE_PATTERNS = [
    ("saturation:objects",   r"OBJECTS OVERFLOW"),
    ("saturation:goals",     r"GOAL(?:S)? STACK OVERFLOW"),
    ("saturation:hyps",      r"TOO MANY HYPOTHESES"),
    ("saturation:seq-ids",   r"SEQUENCE ID NUMBERS OVERFLOW"),
    ("saturation:seq-mem",   r"SEQUENCE MEMORY OVERFLOW"),
    ("saturation:symbols",   r"SYMBOLS OVERFLOW"),
    ("saturation:theories",  r"MAXIMUM NUMBER OF THEORIES .* REACHED"),
    ("saturation:compiler",  r"Compiler Memory Full"),
    ("timer:exceeded",       r"TIMER (?:EXCEEDED|EXPIRED|REAL|VIRTUAL)"),
    ("parse:missing-atom",   r"missing atomic symbol"),
    ("parse:error",          r"(?m)^\s*line\s+\d+:.*(?:error|missing)"),
]


class RunResult:
    __slots__ = ("ok", "stdout", "stderr", "reason")

    def __init__(self, ok, stdout="", stderr="", reason=""):
        self.ok = ok
        self.stdout = stdout
        self.stderr = stderr
        self.reason = reason


def find_tool(name, hints):
    result = subprocess.run(["which", name], capture_output=True, text=True)
    if result.returncode == 0:
        return result.stdout.strip()
    for hint in hints:
        if os.path.exists(hint):
            return hint
    return None


def find_krt():
    return find_tool("krt", ["/opt/atelierb-free-24.04.2/bin/krt"])


def find_replay_kin():
    root = Path(__file__).parent.parent
    for path in [
        root / "atelierb/tools/linux_x64/REPLAY.kin",
        root / "atelierb/tools/macosx/REPLAY.kin",
        Path("/opt/atelierb-free-24.04.2/bin/REPLAY.kin"),
    ]:
        if path.exists():
            return str(path)
    return None


def classify_output(stdout, stderr):
    text = (stdout or "") + "\n" + (stderr or "")
    for reason, pattern in FAILURE_PATTERNS:
        if re.search(pattern, text):
            return reason
    return ""


def run_krt(krt, kin, goal_file, cwd, timeout, timer_setting=None, alloc=None):
    argv = [krt]
    if alloc:
        argv += ["-a", alloc]
    if timer_setting:
        argv += ["-i", timer_setting]
    argv += ["-b", kin, goal_file]
    try:
        result = subprocess.run(
            argv, cwd=cwd, capture_output=True, text=True, timeout=timeout
        )
    except subprocess.TimeoutExpired:
        return RunResult(False, reason="timeout")
    except Exception as exc:
        return RunResult(False, reason=f"exc:{type(exc).__name__}")

    reason = classify_output(result.stdout, result.stderr)
    if reason:
        return RunResult(False, result.stdout, result.stderr, reason)
    if result.returncode != 0:
        return RunResult(False, result.stdout, result.stderr,
                         f"rc={result.returncode}")
    return RunResult(True, result.stdout, result.stderr)


def input_traces(path):
    if path.is_file() and path.suffix == ".trace":
        return [path]
    files = sorted(path.glob("*.trace"))
    if not files:
        raise FileNotFoundError(f"No .trace files in {path}")
    return files


def process_trace(trace_file, out_dir, krt, replay_kin, timeout, timer_setting,
                  alloc, quiet):
    stem = trace_file.stem
    src_dir = trace_file.parent
    goal_path = src_dir / f"{stem}.replay.goal"
    res_name = f"{stem}.replay.res"
    res_path = src_dir / res_name
    replay_path = out_dir / f"{stem}.replay"

    goal_path.write_text(f'Flag(FileOn("{res_name}")) & ("{trace_file}")')
    result = run_krt(
        krt, replay_kin, goal_path.name, str(src_dir), timeout,
        timer_setting=timer_setting, alloc=alloc,
    )

    goal_path.unlink(missing_ok=True)
    res_path.unlink(missing_ok=True)

    misc = src_dir / stem
    if misc.exists() and misc.is_file() and misc.suffix == "":
        misc.unlink()

    if result.ok and result.stdout and len(result.stdout) > 10:
        out_dir.mkdir(parents=True, exist_ok=True)
        replay_path.write_text(result.stdout)
        return True, ""

    reason = result.reason or "empty-output"
    if not quiet:
        print(f"  FAIL REPLAY {stem}: {reason}")
    return False, reason


def main():
    parser = argparse.ArgumentParser(
        description="Generate optional .replay files from .trace files"
    )
    parser.add_argument(
        "input", help="Directory containing .trace files, or one .trace file"
    )
    parser.add_argument(
        "-o", "--output-dir",
        help="Replay output directory (default: next to each .trace file)"
    )
    parser.add_argument("-q", "--quiet", action="store_true")
    parser.add_argument(
        "-t", "--timeout", type=float, default=120.0,
        help="Subprocess wall-clock timeout"
    )
    parser.add_argument(
        "--timer", default="R45",
        help="krt -i timer setting, e.g. R60 or V60. Empty disables it."
    )
    parser.add_argument(
        "--alloc", default="",
        help="krt -a allocation setting. Empty uses krt defaults."
    )
    parser.add_argument("--replay-kin", help="Path to REPLAY.kin")
    parser.add_argument("--krt", help="Path to krt")
    args = parser.parse_args()

    krt = args.krt or find_krt()
    replay_kin = args.replay_kin or find_replay_kin()
    if not krt:
        print("Error: krt not found", file=sys.stderr)
        sys.exit(1)
    if not replay_kin:
        print("Error: REPLAY.kin not found", file=sys.stderr)
        sys.exit(1)

    input_path = Path(args.input).resolve()
    try:
        trace_files = input_traces(input_path)
    except FileNotFoundError as exc:
        print(exc, file=sys.stderr)
        sys.exit(1)

    fixed_out_dir = Path(args.output_dir).resolve() if args.output_dir else None
    if not args.quiet:
        print(f"Processing {len(trace_files)} .trace files")

    ok = 0
    failed = 0
    breakdown = {}
    for trace_file in trace_files:
        out_dir = fixed_out_dir or trace_file.parent
        success, reason = process_trace(
            trace_file, out_dir, krt, replay_kin, args.timeout,
            args.timer or None, args.alloc or None, args.quiet,
        )
        if success:
            ok += 1
        else:
            failed += 1
            breakdown[reason] = breakdown.get(reason, 0) + 1

    print(f"{ok} replays generated" + (f", {failed} failed" if failed else ""))
    if failed and not args.quiet:
        print("Failure breakdown:")
        for reason, count in sorted(breakdown.items()):
            print(f"  {reason:<20} {count}")
    if failed:
        sys.exit(1)


if __name__ == "__main__":
    main()
