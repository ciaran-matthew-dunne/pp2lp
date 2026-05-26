"""Shared helpers for running Atelier B `krt` against PP.kin / REPLAY.kin.

gen_traces.py and gen_replays.py both wrap `krt -b KIN goal-file`.  Anything
specific to the workload (which `.kin`, what failure patterns to recognise)
lives in the caller; this module owns:

  - locating krt and the .kin files,
  - running krt with timeout / classification,
  - the saturation/timer pattern table that every workload shares,
  - the per-file boilerplate (write goal, run, classify, clean up).
"""

import os
import re
import subprocess
from pathlib import Path


# Common krt failure patterns (saturation + timer).  Workload-specific
# additions (e.g. parse errors for REPLAY) get layered in by the caller.
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
]


class RunResult:
    __slots__ = ("ok", "stdout", "stderr", "reason")

    def __init__(self, ok, stdout="", stderr="", reason=""):
        self.ok = ok
        self.stdout = stdout
        self.stderr = stderr
        self.reason = reason


def which(name: str) -> str | None:
    r = subprocess.run(["which", name], capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else None


def find_krt(hints: list[str] | None = None) -> str | None:
    hints = hints or ["/opt/atelierb-free-24.04.2/bin/krt"]
    found = which("krt")
    if found:
        return found
    for h in hints:
        if os.path.exists(h):
            return h
    return None


def find_kin(name: str, hints: list[str | Path]) -> str | None:
    """Find a .kin file by name, falling back to hint paths."""
    for h in hints:
        p = Path(h)
        if p.exists():
            return str(p)
    return None


def classify(stdout: str, stderr: str, patterns) -> str:
    text = (stdout or "") + "\n" + (stderr or "")
    for reason, pattern in patterns:
        if re.search(pattern, text):
            return reason
    return ""


def run_krt(krt, kin, goal_file, cwd, timeout, timer=None, alloc=None,
            patterns=SATURATION_PATTERNS):
    argv = [krt]
    if alloc:
        argv += ["-a", alloc]
    if timer:
        argv += ["-i", timer]
    argv += ["-b", kin, goal_file]
    try:
        r = subprocess.run(argv, cwd=cwd, capture_output=True, text=True,
                           timeout=timeout)
    except subprocess.TimeoutExpired:
        return RunResult(False, reason="timeout")
    except Exception as exc:
        return RunResult(False, reason=f"exc:{type(exc).__name__}")

    reason = classify(r.stdout, r.stderr, patterns)
    if reason:
        return RunResult(False, r.stdout, r.stderr, reason)
    if r.returncode != 0:
        return RunResult(False, r.stdout, r.stderr, f"rc={r.returncode}")
    return RunResult(True, r.stdout, r.stderr)


def gather_inputs(path: Path, suffix: str) -> list[Path]:
    """Return [path] if a single matching file, else all *suffix files in dir."""
    if path.is_file() and path.suffix == suffix:
        return [path]
    files = sorted(path.glob(f"*{suffix}"))
    if not files:
        raise FileNotFoundError(f"No {suffix} files in {path}")
    return files


def add_common_args(parser, default_timer="R45", default_timeout=60.0):
    """Add the standard krt CLI flags shared by gen_traces / gen_replays."""
    src = parser.add_mutually_exclusive_group(required=True)
    src.add_argument("--suite", help="Process lp/bench/SUITE/*")
    src.add_argument("--dir", dest="input_dir",
                     help="Process files under DIR (or one file)")
    parser.add_argument("-o", "--output-dir",
                        help="Output directory (default: next to each input)")
    parser.add_argument("-q", "--quiet", action="store_true")
    parser.add_argument("-t", "--timeout", type=float, default=default_timeout,
                        help="Subprocess wall-clock timeout")
    parser.add_argument("--timer", default=default_timer,
                        help="krt -i timer setting (R45, V60, ...). Empty disables.")
    parser.add_argument("--alloc", default="",
                        help="krt -a allocation setting. Empty uses krt default.")
    parser.add_argument("--krt", help="Path to krt")


def resolve_input_dir(args, root: Path) -> Path:
    if args.suite:
        return (root / "lp" / "bench" / args.suite).resolve()
    return Path(args.input_dir).resolve()


def print_breakdown(label_ok: str, ok: int, failed: int, breakdown: dict):
    print(f"{ok} {label_ok}" + (f", {failed} failed" if failed else ""))
    if failed:
        print("Failure breakdown:")
        for reason, count in sorted(breakdown.items()):
            print(f"  {reason:<20} {count}")
