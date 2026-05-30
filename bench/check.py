#!/usr/bin/env python3
"""Emit + lambdapi-check pp2lp replays."""

import argparse
import os
import re
import subprocess
import sys
import time
from pathlib import Path

try:
    import resource  # POSIX-only; used to cap child address space / CPU
except ImportError:
    resource = None

ROOT = Path(__file__).resolve().parent.parent
PP2LP = ROOT / "ocaml" / "_build" / "default" / "bin" / "main.exe"
FORMATTER = ROOT / "bench" / "format_lambdapi_json.py"

COLOR = sys.stdout.isatty()

# ── Safety caps for child processes ──────────────────────────
# A runaway emit/check (e.g. a goal that sends lambdapi into a memory or
# unification blowup) must never take down the host.  Each child gets a
# wall-clock timeout and — on POSIX — an address-space and CPU-time cap.
# All tunable via env; 0 disables a given cap.
CHECK_TIMEOUT = float(os.environ.get("PP2LP_CHECK_TIMEOUT", "60"))   # lambdapi, seconds
EMIT_TIMEOUT = float(os.environ.get("PP2LP_EMIT_TIMEOUT", "30"))     # pp2lp emit, seconds
CHILD_MEM_GB = float(os.environ.get("PP2LP_CHECK_MEM_GB", "4"))      # RLIMIT_AS, GiB


def _child_limits(timeout: float):
    """Build a preexec_fn that caps the child's address space and CPU time.
    Returns None where unsupported (non-POSIX), so callers can pass it through."""
    if resource is None or os.name != "posix":
        return None

    def apply():
        if CHILD_MEM_GB > 0:
            n = int(CHILD_MEM_GB * 1024 ** 3)
            try:
                resource.setrlimit(resource.RLIMIT_AS, (n, n))
            except (ValueError, OSError):
                pass
        if timeout > 0:
            cpu = int(timeout) + 10  # backstop if the wall-clock timeout can't fire
            try:
                resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu))
            except (ValueError, OSError):
                pass

    return apply


def _c(code, t):
    return f"\033[{code}m{t}\033[0m" if COLOR else str(t)


def _green(t):  return _c("32", t)
def _yellow(t): return _c("33", t)
def _red(t):    return _c("31", t)
def _dim(t):    return _c("2", t)


_ICON = {
    "ok":        _green("✓"),
    "warn":      _yellow("⚠"),
    "emit_fail": _red("✗"),
    "lp_fail":   _red("✗"),
}


def out_path(replay: Path) -> Path:
    return replay.with_suffix(".lp")


def emit(replay: Path, out: Path) -> tuple[bool, list[str], str]:
    out.parent.mkdir(parents=True, exist_ok=True)
    tmp = out.with_suffix(out.suffix + ".tmp")
    try:
        rel_replay = replay.relative_to(ROOT) if replay.is_relative_to(ROOT) else replay
        with tmp.open("w") as fh:
            r = subprocess.run(
                [str(PP2LP), "emit", str(rel_replay)],
                stdout=fh, stderr=subprocess.PIPE, cwd=ROOT,
                timeout=EMIT_TIMEOUT or None,
                preexec_fn=_child_limits(EMIT_TIMEOUT),
                start_new_session=True,
            )
    except FileNotFoundError:
        tmp.unlink(missing_ok=True)
        return False, [], "pp2lp not found; run make build"
    except subprocess.TimeoutExpired:
        tmp.unlink(missing_ok=True)
        return False, [], f"emit timed out after {EMIT_TIMEOUT:.0f}s (PP2LP_EMIT_TIMEOUT)"

    stderr = r.stderr.decode().rstrip()
    warnings, errors = [], []
    for line in stderr.splitlines():
        if line.startswith("WARNING: "):
            warnings.append(line[len("WARNING: "):])
        elif line:
            errors.append(line)

    if r.returncode != 0:
        tmp.unlink(missing_ok=True)
        return False, warnings, "\n".join(errors) if errors else stderr
    tmp.replace(out)
    return True, warnings, ""


def lp_check(lp: Path) -> tuple[bool, str]:
    try:
        r = subprocess.run(
            ["lambdapi", "check", "--json", "-c", str(lp)],
            capture_output=True, text=True,
            timeout=CHECK_TIMEOUT or None,
            preexec_fn=_child_limits(CHECK_TIMEOUT),
            start_new_session=True,
        )
    except subprocess.TimeoutExpired:
        return False, (f"lambdapi check timed out after {CHECK_TIMEOUT:.0f}s "
                       f"(PP2LP_CHECK_TIMEOUT); likely a unification/memory blowup")
    f = subprocess.run(
        [sys.executable, str(FORMATTER)],
        input=r.stdout + r.stderr,
        capture_output=True, text=True,
    )
    return r.returncode == 0, f.stdout


def check_one(replay: Path) -> tuple[str, list[str], str, float, float]:
    out = out_path(replay)
    t0 = time.monotonic()
    ok, warnings, err = emit(replay, out)
    t_emit = time.monotonic() - t0
    if not ok:
        return "emit_fail", warnings, err, t_emit, 0.0
    t1 = time.monotonic()
    ok, text = lp_check(out)
    t_check = time.monotonic() - t1
    if not ok:
        return "lp_fail", warnings, text.rstrip(), t_emit, t_check
    if warnings:
        return "warn", warnings, "", t_emit, t_check
    return "ok", [], "", t_emit, t_check


def select(args, parser) -> list[Path]:
    if args.replay:
        p = Path(args.replay)
        if not p.is_absolute():
            p = (Path.cwd() / p).resolve()
        if not p.exists():
            parser.error(f"replay not found: {p}")
        return [p]
    if args.name:
        if not args.suite:
            parser.error("--name requires --suite")
        p = ROOT / "lp" / "bench" / args.suite / f"{args.name}.replay"
        if not p.exists():
            p_xfail = ROOT / "lp" / "bench" / args.suite / "xfail" / f"{args.name}.replay"
            if p_xfail.exists():
                p = p_xfail
        if not p.exists():
            parser.error(f"replay not found: {p}")
        return [p]
    if args.suite:
        d = ROOT / "lp" / "bench" / args.suite
        replays = sorted(d.glob("*.replay"))
        if not replays:
            parser.error(f"no .replay files under {d}")
        return replays
    parser.error("need --suite, --replay, or --name --suite")


def load_expected_fail(suite: str) -> set:
    """Goal stems known to fail `lambdapi check` for this suite — the gate
    baseline.  One name per line in lp/bench/<suite>/expected_fail.txt; blank
    lines and `#` comments are ignored.  An absent file yields the empty set, so
    every failure breaks the gate (this keeps og a hard 100-percent gate)."""
    path = ROOT / "lp" / "bench" / suite / "expected_fail.txt"
    if not path.exists():
        return set()
    names = set()
    for raw in path.read_text().splitlines():
        line = raw.split("#", 1)[0].strip()
        if line:
            names.add(line)
    return names


def fmt_ms(ms: float) -> str:
    return f"{ms / 1000:.1f}s" if ms >= 1000 else f"{ms:.0f}ms"


_RE_PATH_PREFIX = re.compile(
    r'^(?:tree-build error in|parse error in) \S+:\s*'
    r'|'
    r'^\S+\.replay:\s*'
)


def _clean_error(text: str) -> str:
    lines = []
    for line in text.splitlines():
        line = _RE_PATH_PREFIX.sub('', line)
        lines.append(line)
    return "\n".join(lines)


def print_entry(name: str, status: str, warnings: list[str],
                detail: str, show_time: bool, emit_ms: float, check_ms: float,
                suffix: str = ""):
    if show_time:
        if check_ms > 0:
            time_str = f"  {_dim(f'emit {fmt_ms(emit_ms)} / check {fmt_ms(check_ms)}')}"
        else:
            time_str = f"  {_dim(f'emit {fmt_ms(emit_ms)}')}"
    else:
        time_str = ""
    print(f" {_ICON[status]} {name}{suffix}{time_str}")
    for w in warnings:
        print(f"   {_dim(w)}")
    if detail:
        for line in _clean_error(detail).splitlines():
            print(f"   {line}")


def main():
    ap = argparse.ArgumentParser(description="Emit + lambdapi-check pp2lp replays.")
    ap.add_argument("--suite", help="lp/bench/SUITE/")
    ap.add_argument("--name", help="replay stem under lp/bench/SUITE/")
    ap.add_argument("--replay", help="path to a .replay file")
    ap.add_argument("-q", "--quiet", action="store_true", help="summary only")
    ap.add_argument("-v", "--verbose", action="store_true", help="show all replays")
    args = ap.parse_args()

    replays = select(args, ap)
    single = len(replays) == 1
    show_ok = args.verbose or single
    show_lines = not args.quiet
    show_time = args.verbose or single
    expected_fail = load_expected_fail(args.suite) if args.suite else set()

    counts = {"ok": 0, "warn": 0, "emit_fail": 0, "lp_fail": 0}
    total_emit = 0.0
    total_check = 0.0
    t_start = time.monotonic()
    xfail = []        # in the baseline and did fail — expected, gate-neutral
    xpass = []        # in the baseline but passed — stale entry, breaks the gate
    unexpected = []   # not in the baseline but failed — breaks the gate

    for t in replays:
        status, warnings, detail, t_emit, t_check = check_one(t)
        counts[status] += 1
        total_emit += t_emit
        total_check += t_check

        failed = status in ("emit_fail", "lp_fail")
        known = t.stem in expected_fail
        if failed and known:
            xfail.append(t.stem)
        elif failed:
            unexpected.append(t.stem)
        elif known:
            xpass.append(t.stem)

        if not show_lines:
            continue
        if status == "ok" and not show_ok and not known:
            continue

        # In a bulk run, mute the verbose diagnostic for KNOWN failures so the
        # gate output stays readable; a single-trace or -v run still shows it.
        suppress = failed and known and not single and not args.verbose
        if failed and known:
            suffix = _dim(" (expected)")
        elif known and not failed:
            suffix = _yellow(" (UNEXPECTED PASS — prune expected_fail.txt)")
        else:
            suffix = ""
        print_entry(t.stem, status, warnings, "" if suppress else detail,
                    show_time, t_emit * 1000, t_check * 1000, suffix)

    elapsed_total = (time.monotonic() - t_start) * 1000

    if not single or args.verbose:
        parts = []
        if counts["ok"]:
            parts.append(f"{_green(counts['ok'])} ✓")
        if counts["warn"]:
            parts.append(f"{_yellow(counts['warn'])} ⚠")
        if unexpected:
            parts.append(f"{_red(len(unexpected))} ✗")
        if xfail:
            parts.append(_dim(f"{len(xfail)} xfail"))
        if xpass:
            parts.append(_yellow(f"{len(xpass)} xpass"))

        suite = args.suite or "check"
        if show_lines:
            print()
        breakdown = _dim(
            f"emit {fmt_ms(total_emit * 1000)} / check {fmt_ms(total_check * 1000)}"
        )
        print(f"{suite}  {'  '.join(parts)}  {_dim(fmt_ms(elapsed_total))}  {breakdown}")

    # Gate fails on any deviation from the baseline: an unexpected failure, or a
    # stale expected_fail.txt entry that now passes.
    sys.exit(1 if (unexpected or xpass) else 0)


if __name__ == "__main__":
    main()
