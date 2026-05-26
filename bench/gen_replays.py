#!/usr/bin/env python3
"""Generate optional PP `.replay` files from existing `.trace` files.

Replays are debugging artifacts only.  pp2lp reads traces directly and
does not consume these files.
"""

import argparse
import sys
from pathlib import Path

import _krt


# REPLAY has its own parse-error patterns on top of the shared saturation set.
REPLAY_EXTRA = [
    ("parse:missing-atom",   r"missing atomic symbol"),
    ("parse:error",          r"(?m)^\s*line\s+\d+:.*(?:error|missing)"),
]
PATTERNS = _krt.SATURATION_PATTERNS + REPLAY_EXTRA


def find_replay_kin():
    root = Path(__file__).resolve().parent.parent
    return _krt.find_kin("REPLAY.kin", [
        root / "atelierb/tools/linux_x64/REPLAY.kin",
        root / "atelierb/tools/macosx/REPLAY.kin",
        "/opt/atelierb-free-24.04.2/bin/REPLAY.kin",
    ])


def process_trace(trace_file, out_dir, krt, replay_kin, timeout, timer,
                  alloc, quiet):
    stem = trace_file.stem
    src_dir = trace_file.parent
    goal_path = src_dir / f"{stem}.replay.goal"
    res_name = f"{stem}.replay.res"
    res_path = src_dir / res_name
    replay_path = out_dir / f"{stem}.replay"

    goal_path.write_text(f'Flag(FileOn("{res_name}")) & ("{trace_file}")')
    result = _krt.run_krt(krt, replay_kin, goal_path.name, str(src_dir),
                          timeout, timer=timer, alloc=alloc, patterns=PATTERNS)

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
    _krt.add_common_args(parser, default_timer="R45", default_timeout=120.0)
    parser.add_argument("--replay-kin", help="Path to REPLAY.kin")
    args = parser.parse_args()

    krt = args.krt or _krt.find_krt()
    replay_kin = args.replay_kin or find_replay_kin()
    if not krt:
        print("Error: krt not found", file=sys.stderr); sys.exit(1)
    if not replay_kin:
        print("Error: REPLAY.kin not found", file=sys.stderr); sys.exit(1)

    root = Path(__file__).resolve().parent.parent
    input_path = _krt.resolve_input_dir(args, root)
    try:
        traces = _krt.gather_inputs(input_path, ".trace")
    except FileNotFoundError as exc:
        print(exc, file=sys.stderr); sys.exit(1)

    fixed_out = Path(args.output_dir).resolve() if args.output_dir else None
    if not args.quiet:
        print(f"Processing {len(traces)} .trace files")

    ok = failed = 0
    breakdown = {}
    for trace in traces:
        out_dir = fixed_out or trace.parent
        success, reason = process_trace(
            trace, out_dir, krt, replay_kin, args.timeout,
            args.timer or None, args.alloc or None, args.quiet,
        )
        if success:
            ok += 1
        else:
            failed += 1
            breakdown[reason] = breakdown.get(reason, 0) + 1

    _krt.print_breakdown("replays generated", ok, failed, breakdown)
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
