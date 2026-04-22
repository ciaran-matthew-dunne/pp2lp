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


# krt saturation / failure patterns. Matched against merged stdout+stderr
# AFTER a krt run — krt exits 0 even when it fails to prove, so these patterns
# are the only way to detect resource exhaustion or internal stops.
#
# Keys become gen_status reasons like "saturation:objects".
SATURATION_PATTERNS = [
    ("saturation:objects",   r"OBJECTS OVERFLOW"),
    ("saturation:goals",     r"GOAL(?:S)? STACK OVERFLOW"),
    ("saturation:hyps",      r"TOO MANY HYPOTHESES"),
    ("saturation:seq-ids",   r"SEQUENCE ID NUMBERS OVERFLOW"),
    ("saturation:seq-mem",   r"SEQUENCE MEMORY OVERFLOW"),
    ("saturation:symbols",   r"SYMBOLS OVERFLOW"),
    ("saturation:theories",  r"MAXIMUM NUMBER OF THEORIES .* REACHED"),
    ("saturation:compiler",  r"Compiler Memory Full"),
    ("timer:exceeded",       r"TIMER (?:EXCEEDED|EXPIRED|REAL|VIRTUAL)"),
    # REPLAY surfaces these on malformed / truncated traces (often the
    # downstream symptom of PP giving up partway through writing).
    ("parse:missing-atom",   r"missing atomic symbol"),
    ("parse:error",          r"(?m)^\s*line\s+\d+:.*(?:error|missing)"),
]


def classify_krt_output(stdout, stderr):
    """Scan krt output for known failure/saturation markers.
    Returns a reason string (e.g. 'saturation:objects') or '' if none found.
    """
    text = (stdout or "") + "\n" + (stderr or "")
    for reason, pat in SATURATION_PATTERNS:
        if re.search(pat, text):
            return reason
    return ""


class RunResult:
    """Outcome of a krt invocation."""
    __slots__ = ("ok", "stdout", "stderr", "reason")

    def __init__(self, ok, stdout=None, stderr=None, reason=""):
        self.ok = ok
        self.stdout = stdout
        self.stderr = stderr
        # Reason taxonomy:
        #   ""                     — success
        #   "timeout"              — subprocess hard timeout (shouldn't fire if -i used)
        #   "rc=N"                 — krt exited nonzero (malformed input, etc.)
        #   "saturation:<kind>"    — krt printed a resource-exhaustion marker
        #   "timer:exceeded"       — krt's internal -i timer fired
        #   "exc:<Class>"          — Python exception
        #   "empty-output"         — krt returned no usable stdout
        self.reason = reason

    def __bool__(self):
        return self.ok


def run_krt(krt, kin, goal_file, cwd, timeout, capture_stdout=False,
            timer_setting=None, alloc=None):
    """Run krt and return a RunResult with a classified failure reason.

    timer_setting: optional krt -i argument like "R60" (real) or "V60" (virtual).
    When set, krt self-bounds proof time and exits cleanly with diagnostics;
    the subprocess-level timeout then acts as a safety net only.
    alloc: optional krt -a argument like "h20000g20000o200000" — tunes
    internal stacks/capacities. See `krt -h` for the letter/number grammar.
    """
    argv = [krt]
    if alloc:
        argv += ["-a", alloc]
    if timer_setting:
        argv += ["-i", timer_setting]
    argv += ["-b", kin, goal_file]
    try:
        r = subprocess.run(
            argv, cwd=cwd, capture_output=True, text=True, timeout=timeout
        )
        stdout = r.stdout if capture_stdout else None
        # krt frequently exits 0 even when it fails to prove (saturation,
        # timer). Always scan output for saturation markers to distinguish
        # real success from "exited cleanly but gave up".
        sat = classify_krt_output(r.stdout, r.stderr)
        if sat:
            return RunResult(False, stdout, r.stderr, sat)
        if r.returncode == 0:
            return RunResult(True, stdout, r.stderr)
        return RunResult(False, stdout, r.stderr, f"rc={r.returncode}")
    except subprocess.TimeoutExpired:
        return RunResult(False, None, None, "timeout")
    except Exception as e:
        return RunResult(False, None, None, f"exc:{type(e).__name__}")


def process_but(but_file: Path, krt, pp_kin, replay_kin, out_dir: Path,
                pp_timeout, replay_timeout, quiet, timer_setting=None,
                alloc=None):
    """Process one .but file → .replay in out_dir.

    Returns (success, stage, reason). On success stage/reason are "", "".
    On failure stage ∈ {"pp", "replay"} and reason classifies why.
    """
    stem = but_file.stem
    src_dir = but_file.parent

    but_content = but_file.read_text()

    # Create .goal for PP with TraceOn + FileOn pointing at our stem.
    # Strip any pre-existing TypeOn/TraceOn/FileOn flags so we don't duplicate
    # them (bug: duplicate TraceOn causes PP to exit with rc=1 on PRV goals
    # whose .but files already include their own Trace/File flags).
    trace_file = f"{stem}.trace"
    res_file = f"{stem}.res"
    goal_content = but_content
    goal_content = re.sub(r'Flag\(TypeOn\([^)]+\)\)\s*&\s*', '', goal_content)
    goal_content = re.sub(r'Flag\(TraceOn\([^)]+\)\)\s*&\s*', '', goal_content)
    goal_content = re.sub(r'Flag\(FileOn\([^)]+\)\)\s*&\s*', '', goal_content)
    goal_content = (f'Flag(TraceOn("{trace_file}")) & '
                    f'Flag(FileOn("{res_file}")) & {goal_content}')

    goal_path = src_dir / f"{stem}.goal"
    goal_path.write_text(goal_content)

    # Run PP
    pp = run_krt(krt, pp_kin, goal_path.name, str(src_dir), pp_timeout,
                 timer_setting=timer_setting, alloc=alloc)

    trace_path = src_dir / trace_file
    res_path = src_dir / res_file

    # Cleanup goal + res
    goal_path.unlink(missing_ok=True)
    res_path.unlink(missing_ok=True)

    if not pp.ok:
        if not quiet:
            print(f"  FAIL PP  {stem}: {pp.reason}")
        trace_path.unlink(missing_ok=True)
        return False, "pp", pp.reason
    # Trace may be missing, zero-length, or BOM-only (3-byte UTF-8 BOM with
    # nothing after — PP opens the file but exits before writing any content).
    # Treat any of these as an empty trace.
    trace_empty = True
    if trace_path.exists():
        data = trace_path.read_bytes()
        if data.startswith(b"\xef\xbb\xbf"):
            data = data[3:]
        trace_empty = len(data.strip()) == 0
    if trace_empty:
        if not quiet:
            print(f"  FAIL PP  {stem}: empty-trace")
        trace_path.unlink(missing_ok=True)
        return False, "pp", "empty-trace"

    # Create replay goal
    replay_goal = src_dir / f"{stem}.replay.goal"
    replay_res = f"{stem}.replay.res"
    replay_goal.write_text(
        f'Flag(FileOn("{replay_res}")) & ("{trace_path}")'
    )

    # Run REPLAY
    rep = run_krt(krt, replay_kin, replay_goal.name, str(src_dir),
                  replay_timeout, capture_stdout=True,
                  timer_setting=timer_setting, alloc=alloc)

    # Cleanup intermediates (keep .trace for debugging)
    replay_goal.unlink(missing_ok=True)
    (src_dir / replay_res).unlink(missing_ok=True)
    # Clean misc files without extension
    misc = src_dir / stem
    if misc.exists() and misc.is_file() and misc.suffix == "":
        misc.unlink()

    if rep.ok and rep.stdout and len(rep.stdout) > 10:
        replay_out = out_dir / f"{stem}.replay"
        replay_out.write_text(rep.stdout)
        return True, "", ""
    reason = rep.reason or "empty-output"
    if not quiet:
        print(f"  FAIL REP {stem}: {reason}")
    return False, "replay", reason


def main():
    parser = argparse.ArgumentParser(description="Generate PP replays from .but files")
    parser.add_argument("directory", help="Directory containing .but files, or a single .but file")
    parser.add_argument("-o", "--output-dir", help="Output dir for .replay files (default: <dir>)")
    parser.add_argument("-q", "--quiet", action="store_true")
    parser.add_argument("-f", "--force", action="store_true",
                        help="Regenerate all replays (ignore timestamps)")
    parser.add_argument("-t", "--timeout", type=float, default=60.0,
                        help="Subprocess wall-clock timeout (safety net; krt's -i timer is preferred)")
    parser.add_argument("--timer", default="R45",
                        help="krt -i timer_setting, e.g. R60 (real, 60s) or V60 (virtual). "
                             "Set to '' to disable. Default: R45")
    parser.add_argument("--alloc", default="",
                        help="krt -a alloc_setting, e.g. h20000g20000o200000. "
                             "Bumps internal stacks/capacities. Default: krt builtin defaults.")
    parser.add_argument("--pp-kin", help="Path to PP.kin")
    parser.add_argument("--replay-kin", help="Path to REPLAY.kin")
    parser.add_argument("--krt", help="Path to krt")
    args = parser.parse_args()
    # Empty --timer / --alloc means "use krt defaults"
    timer_setting = args.timer or None
    alloc = args.alloc or None

    krt = args.krt or find_krt()
    pp_kin = args.pp_kin or find_pp_kin()
    replay_kin = args.replay_kin or find_replay_kin()

    if not krt:
        print("Error: krt not found", file=sys.stderr); sys.exit(1)
    if not pp_kin:
        print("Error: PP.kin not found", file=sys.stderr); sys.exit(1)
    if not replay_kin:
        print("Error: REPLAY.kin not found", file=sys.stderr); sys.exit(1)

    src_path = Path(args.directory).resolve()
    if src_path.is_file() and src_path.suffix == ".but":
        src_dir = src_path.parent
        but_files = [src_path]
    else:
        src_dir = src_path
        but_files = sorted(src_dir.glob("*.but"))
        if not but_files:
            print(f"No .but files in {src_dir}")
            sys.exit(1)

    out_dir = Path(args.output_dir).resolve() if args.output_dir else src_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    if not args.quiet:
        print(f"Processing {len(but_files)} .but files")

    succeeded = 0
    failed = 0
    skipped = 0
    # Breakdown: stage → reason → count
    breakdown = {}
    # Per-test status log (aggregate only when operating on a directory, not
    # on a single .but file, so single-file invocations don't clobber the log).
    is_dir_run = src_path.is_dir() and args.output_dir is not None
    status_log = out_dir / ".gen_status.tsv"
    existing_status = {}
    if is_dir_run and status_log.exists():
        for line in status_log.read_text().splitlines():
            parts = line.split("\t")
            if len(parts) >= 2:
                existing_status[parts[0]] = parts[1:]

    new_status = dict(existing_status) if is_dir_run else {}

    for bf in but_files:
        stem = bf.stem
        # Incremental: skip if replay is newer than .but
        if not args.force:
            replay_path = out_dir / f"{stem}.replay"
            if (replay_path.exists()
                    and replay_path.stat().st_mtime >= bf.stat().st_mtime):
                succeeded += 1
                skipped += 1
                if is_dir_run:
                    new_status[stem] = ["cached", ""]
                continue

        ok, stage, reason = process_but(
            bf, krt, pp_kin, replay_kin, out_dir,
            args.timeout, args.timeout * 2, args.quiet,
            timer_setting=timer_setting, alloc=alloc,
        )
        if ok:
            succeeded += 1
            if is_dir_run:
                new_status[stem] = ["ok", ""]
        else:
            failed += 1
            breakdown.setdefault(stage, {})
            breakdown[stage][reason] = breakdown[stage].get(reason, 0) + 1
            if is_dir_run:
                new_status[stem] = [f"fail-{stage}", reason]

    if is_dir_run:
        lines = [f"{name}\t{st[0]}\t{st[1]}" for name, st in sorted(new_status.items())]
        status_log.write_text("\n".join(lines) + "\n")

    parts = [f"{succeeded} replayed"]
    if failed:
        parts.append(f"{failed} failed")
    if skipped:
        parts.append(f"{skipped} cached")
    print(", ".join(parts))

    if failed and not args.quiet:
        print("Failure breakdown:")
        for stage in sorted(breakdown):
            for reason, n in sorted(breakdown[stage].items()):
                print(f"  {stage:<7} {reason:<20} {n}")


if __name__ == "__main__":
    main()
