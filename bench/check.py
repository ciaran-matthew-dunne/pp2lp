#!/usr/bin/env python3
"""Emit + lambdapi-check pp2lp replays."""

import argparse
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PP2LP = ROOT / "ocaml" / "_build" / "default" / "bin" / "main.exe"
FORMATTER = ROOT / "bench" / "format_lambdapi_json.py"

COLOR = sys.stdout.isatty()


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
            )
    except FileNotFoundError:
        tmp.unlink(missing_ok=True)
        return False, [], "pp2lp not found; run make build"

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
    r = subprocess.run(
        ["lambdapi", "check", "--json", "-c", str(lp)],
        capture_output=True, text=True,
    )
    f = subprocess.run(
        [sys.executable, str(FORMATTER)],
        input=r.stdout + r.stderr,
        capture_output=True, text=True,
    )
    return r.returncode == 0, f.stdout


def check_one(replay: Path) -> tuple[str, list[str], str, float]:
    t0 = time.monotonic()
    out = out_path(replay)
    ok, warnings, err = emit(replay, out)
    if not ok:
        return "emit_fail", warnings, err, time.monotonic() - t0
    ok, text = lp_check(out)
    if not ok:
        return "lp_fail", warnings, text.rstrip(), time.monotonic() - t0
    if warnings:
        return "warn", warnings, "", time.monotonic() - t0
    return "ok", [], "", time.monotonic() - t0


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
                detail: str, show_time: bool, ms: float):
    time_str = f"  {_dim(fmt_ms(ms))}" if show_time else ""
    print(f" {_ICON[status]} {name}{time_str}")
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

    counts = {"ok": 0, "warn": 0, "emit_fail": 0, "lp_fail": 0}
    t_start = time.monotonic()

    for t in replays:
        status, warnings, detail, elapsed = check_one(t)
        counts[status] += 1

        if not show_lines:
            continue
        if status == "ok" and not show_ok:
            continue

        print_entry(t.stem, status, warnings, detail, show_time, elapsed * 1000)

    elapsed_total = (time.monotonic() - t_start) * 1000
    n_fail = counts["emit_fail"] + counts["lp_fail"]

    if not single or args.verbose:
        parts = []
        if counts["ok"]:
            parts.append(f"{_green(counts['ok'])} ✓")
        if counts["warn"]:
            parts.append(f"{_yellow(counts['warn'])} ⚠")
        if n_fail:
            parts.append(f"{_red(n_fail)} ✗")

        suite = args.suite or "check"
        if show_lines:
            print()
        print(f"{suite}  {'  '.join(parts)}  {_dim(fmt_ms(elapsed_total))}")

    sys.exit(0 if n_fail == 0 else 1)


if __name__ == "__main__":
    main()
