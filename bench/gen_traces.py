#!/usr/bin/env python3
"""Generate PP traces and replays from .but files.

Pipeline: .but → PP → .trace → REPLAY → .replay
Intermediate .res and .goal files are cleaned up.
The .trace files are kept for debugging.

Usage:
    python3 gen_traces.py [options] <directory-with-but-files>
    python3 gen_traces.py -q -o bench/gen bench/gen
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Optional


def find_tool(name, hints):
    """Find a binary on PATH or at known locations."""
    result = subprocess.run(["which", name], capture_output=True, text=True)
    if result.returncode == 0:
        return result.stdout.strip()
    for h in hints:
        if os.path.exists(h):
            return h
    return None


def find_krt():
    return find_tool("krt", ["/opt/atelierb-free-24.04.2/bin/krt"])


def find_pp_kin():
    for p in ["/opt/atelierb-free-24.04.2/bin/PP.kin",
              os.path.expanduser("~/atelierb/bin/PP.kin")]:
        if os.path.exists(p):
            return p
    return None


def find_replay_kin():
    script_dir = Path(__file__).parent.parent
    for p in [script_dir / "atelierb/tools/linux_x64/REPLAY.kin",
              script_dir / "atelierb/tools/macosx/REPLAY.kin",
              Path("/opt/atelierb-free-24.04.2/bin/REPLAY.kin")]:
        if p.exists():
            return str(p)
    return None


def run_krt(krt, kin, goal_file, cwd, timeout, capture_stdout=False):
    """Run krt and return (success, stdout_or_None)."""
    try:
        r = subprocess.run(
            [krt, "-b", kin, goal_file],
            cwd=cwd, capture_output=True, text=True, timeout=timeout
        )
        stdout = r.stdout if capture_stdout else None
        return r.returncode == 0, stdout
    except subprocess.TimeoutExpired:
        return False, None
    except Exception:
        return False, None


def process_but(but_file: Path, krt, pp_kin, replay_kin, out_dir: Path,
                pp_timeout, replay_timeout, quiet):
    """Process one .but file → .replay in out_dir. Returns True on success."""
    stem = but_file.stem
    src_dir = but_file.parent

    but_content = but_file.read_text()

    # Create .goal for PP (TraceOn)
    trace_file = f"{stem}.trace"
    res_file = f"{stem}.res"
    goal_content = re.sub(r'Flag\(TypeOn\([^)]+\)\)\s*&\s*', '', but_content)
    if 'Flag(FileOn(' in goal_content:
        goal_content = re.sub(
            r'Flag\(FileOn\("([^"]+)"\)\)',
            f'Flag(TraceOn("{trace_file}")) & Flag(FileOn("{res_file}"))',
            goal_content
        )
    else:
        goal_content = f'Flag(TraceOn("{trace_file}")) & Flag(FileOn("{res_file}")) & {goal_content}'

    goal_path = src_dir / f"{stem}.goal"
    goal_path.write_text(goal_content)

    # Run PP
    ok, _ = run_krt(krt, pp_kin, goal_path.name, str(src_dir), pp_timeout)

    trace_path = src_dir / trace_file
    res_path = src_dir / res_file

    # Cleanup goal + res
    goal_path.unlink(missing_ok=True)
    res_path.unlink(missing_ok=True)

    if not ok or not trace_path.exists() or trace_path.stat().st_size == 0:
        if not quiet:
            print(f"  FAIL: PP failed for {stem}")
        trace_path.unlink(missing_ok=True)
        return False

    # Create replay goal
    replay_goal = src_dir / f"{stem}.replay.goal"
    replay_res = f"{stem}.replay.res"
    replay_goal.write_text(
        f'Flag(FileOn("{replay_res}")) & ("{trace_path}")'
    )

    # Run REPLAY
    ok, stdout = run_krt(krt, replay_kin, replay_goal.name, str(src_dir),
                         replay_timeout, capture_stdout=True)

    # Cleanup intermediates (keep .trace for debugging)
    replay_goal.unlink(missing_ok=True)
    (src_dir / replay_res).unlink(missing_ok=True)
    # Clean misc files without extension
    misc = src_dir / stem
    if misc.exists() and misc.is_file() and misc.suffix == "":
        misc.unlink()

    if ok and stdout and len(stdout) > 10:
        replay_out = out_dir / f"{stem}.replay"
        replay_out.write_text(stdout)
        return True
    else:
        if not quiet:
            print(f"  FAIL: REPLAY failed for {stem}")
        return False


def main():
    parser = argparse.ArgumentParser(description="Generate PP replays from .but files")
    parser.add_argument("directory", help="Directory containing .but files")
    parser.add_argument("-o", "--output-dir", help="Output dir for .replay files (default: <dir>)")
    parser.add_argument("-q", "--quiet", action="store_true")
    parser.add_argument("-t", "--timeout", type=float, default=60.0)
    parser.add_argument("--pp-kin", help="Path to PP.kin")
    parser.add_argument("--replay-kin", help="Path to REPLAY.kin")
    parser.add_argument("--krt", help="Path to krt")
    args = parser.parse_args()

    krt = args.krt or find_krt()
    pp_kin = args.pp_kin or find_pp_kin()
    replay_kin = args.replay_kin or find_replay_kin()

    if not krt:
        print("Error: krt not found", file=sys.stderr); sys.exit(1)
    if not pp_kin:
        print("Error: PP.kin not found", file=sys.stderr); sys.exit(1)
    if not replay_kin:
        print("Error: REPLAY.kin not found", file=sys.stderr); sys.exit(1)

    src_dir = Path(args.directory).resolve()
    out_dir = Path(args.output_dir).resolve() if args.output_dir else src_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    but_files = sorted(src_dir.glob("*.but"))
    if not but_files:
        print(f"No .but files in {src_dir}")
        sys.exit(1)

    if not args.quiet:
        print(f"Processing {len(but_files)} .but files")

    succeeded = 0
    failed = 0
    for bf in but_files:
        if process_but(bf, krt, pp_kin, replay_kin, out_dir,
                       args.timeout, args.timeout * 2, args.quiet):
            succeeded += 1
        else:
            failed += 1

    parts = [f"{succeeded} replayed"]
    if failed:
        parts.append(f"{failed} failed")
    print(", ".join(parts))


if __name__ == "__main__":
    main()
