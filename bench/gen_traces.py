#!/usr/bin/env python3
"""Generate PP `.trace` files from `.but` files.

Pipeline: .but -> PP -> .trace

Does not run REPLAY and does not cache.  Replays are optional debugging
artifacts; use `bench/gen_replays.py` when you want them.
"""

import argparse
import os
import re
import sys
from pathlib import Path

import _krt


def find_pp_kin():
    return _krt.find_kin("PP.kin", [
        "/opt/atelierb-free-24.04.2/bin/PP.kin",
        os.path.expanduser("~/atelierb/bin/PP.kin"),
    ])


def strip_existing_flags(content: str) -> str:
    for pat in (r'Flag\(TypeOn\([^)]+\)\)\s*&\s*',
                r'Flag\(TraceOn\([^)]+\)\)\s*&\s*',
                r'Flag\(FileOn\([^)]+\)\)\s*&\s*'):
        content = re.sub(pat, '', content)
    return content


def trace_is_empty(path: Path) -> bool:
    if not path.exists():
        return True
    data = path.read_bytes()
    if data.startswith(b"\xef\xbb\xbf"):
        data = data[3:]
    return len(data.strip()) == 0


def process_but(but_file, out_dir, krt, pp_kin, timeout, timer, alloc, quiet):
    stem = but_file.stem
    src_dir = but_file.parent
    out_trace = out_dir / f"{stem}.trace"
    same_output_dir = src_dir.resolve() == out_dir.resolve()
    trace_name = f"{stem}.trace" if same_output_dir else f"{stem}.trace.tmp"
    res_name = f"{stem}.res"

    goal_content = strip_existing_flags(but_file.read_text())
    goal_content = (
        f'Flag(TraceOn("{trace_name}")) & '
        f'Flag(FileOn("{res_name}")) & {goal_content}'
    )

    goal_path = src_dir / f"{stem}.goal"
    src_trace = src_dir / trace_name
    src_res = src_dir / res_name

    goal_path.write_text(goal_content)
    result = _krt.run_krt(krt, pp_kin, goal_path.name, str(src_dir), timeout,
                          timer=timer, alloc=alloc)

    goal_path.unlink(missing_ok=True)
    src_res.unlink(missing_ok=True)

    if not result.ok:
        src_trace.unlink(missing_ok=True)
        if not quiet:
            print(f"  FAIL PP {stem}: {result.reason}")
        return False, result.reason

    if trace_is_empty(src_trace):
        src_trace.unlink(missing_ok=True)
        if not quiet:
            print(f"  FAIL PP {stem}: empty-trace")
        return False, "empty-trace"

    out_dir.mkdir(parents=True, exist_ok=True)
    if not same_output_dir:
        out_trace.write_bytes(src_trace.read_bytes())
        src_trace.unlink()
    return True, ""


def main():
    parser = argparse.ArgumentParser(
        description="Generate PP .trace files from .but files"
    )
    _krt.add_common_args(parser, default_timer="R45", default_timeout=60.0)
    parser.add_argument("--pp-kin", help="Path to PP.kin")
    args = parser.parse_args()

    krt = args.krt or _krt.find_krt()
    pp_kin = args.pp_kin or find_pp_kin()
    if not krt:
        print("Error: krt not found", file=sys.stderr); sys.exit(1)
    if not pp_kin:
        print("Error: PP.kin not found", file=sys.stderr); sys.exit(1)

    root = Path(__file__).resolve().parent.parent
    input_path = _krt.resolve_input_dir(args, root)
    try:
        but_files = _krt.gather_inputs(input_path, ".but")
    except FileNotFoundError as exc:
        print(exc, file=sys.stderr); sys.exit(1)

    fixed_out = Path(args.output_dir).resolve() if args.output_dir else None
    if not args.quiet:
        print(f"Processing {len(but_files)} .but files")

    ok = failed = 0
    breakdown = {}
    for but in but_files:
        out_dir = fixed_out or but.parent
        success, reason = process_but(
            but, out_dir, krt, pp_kin, args.timeout,
            args.timer or None, args.alloc or None, args.quiet,
        )
        if success:
            ok += 1
        else:
            failed += 1
            breakdown[reason] = breakdown.get(reason, 0) + 1

    _krt.print_breakdown("traces generated", ok, failed, breakdown)
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
