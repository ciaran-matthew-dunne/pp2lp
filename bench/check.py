#!/usr/bin/env python3
"""Emit + lambdapi-check pp2lp replays.

Selection (any one):
  --suite SUITE              all bench/SUITE/*.replay
  --replay PATH              one replay by path
  --name NAME --suite SUITE  bench/SUITE/NAME.replay

Output:
  default     one line per replay, error stanza on failure, summary at end
  --quiet     summary only (no per-replay lines)
  --verbose   per-replay lines include OK + timing
"""

import argparse
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PP2LP = ROOT / "ocaml" / "_build" / "default" / "bin" / "main.exe"
FORMATTER = ROOT / "bench" / "format_lambdapi_json.py"


def rel(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def out_path(replay: Path) -> Path:
    return replay.with_suffix(".lp")


def emit(replay: Path, out: Path) -> tuple[bool, str]:
    out.parent.mkdir(parents=True, exist_ok=True)
    tmp = out.with_suffix(out.suffix + ".tmp")
    try:
        with tmp.open("w") as fh:
            r = subprocess.run(
                [str(PP2LP), "emit", str(replay)],
                stdout=fh, stderr=subprocess.PIPE,
            )
    except FileNotFoundError:
        tmp.unlink(missing_ok=True)
        return False, f"pp2lp binary not found at {PP2LP}; run `make build`."
    if r.returncode != 0:
        tmp.unlink(missing_ok=True)
        return False, r.stderr.decode().rstrip()
    tmp.replace(out)
    return True, ""


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


def check_one(replay: Path) -> tuple[str, str, float]:
    """Return (status, detail, elapsed_seconds).

    status is one of: ok, emit_fail, lp_fail.
    detail is the diagnostic text (empty for ok).
    """
    t0 = time.monotonic()
    out = out_path(replay)
    ok, err = emit(replay, out)
    if not ok:
        return "emit_fail", err, time.monotonic() - t0
    ok, text = lp_check(out)
    if not ok:
        return "lp_fail", text.rstrip(), time.monotonic() - t0
    return "ok", "", time.monotonic() - t0


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


def fmt_line(label: str, replay: Path, ms: float) -> str:
    return f"{label} {rel(replay)} ({ms:.0f}ms)"


def main():
    ap = argparse.ArgumentParser(
        description="Emit + lambdapi-check pp2lp replays."
    )
    ap.add_argument("--suite", help="lp/bench/SUITE/")
    ap.add_argument("--name", help="replay stem under lp/bench/SUITE/")
    ap.add_argument("--replay", help="path to a .replay file")
    ap.add_argument("-q", "--quiet", action="store_true",
                    help="summary only")
    ap.add_argument("-v", "--verbose", action="store_true",
                    help="include OK lines in output")
    args = ap.parse_args()

    replays = select(args, ap)

    # When checking a single replay, default to verbose-style output.
    single = len(replays) == 1
    show_ok = args.verbose or single
    show_lines = not args.quiet

    ok = lp_fail = emit_fail = 0
    failures: list[tuple[str, Path, str]] = []

    for t in replays:
        status, detail, elapsed = check_one(t)
        ms = elapsed * 1000

        if status == "ok":
            ok += 1
            if show_ok and show_lines:
                print(fmt_line("ok   ", t, ms))
        else:
            if status == "emit_fail":
                emit_fail += 1
            else:
                lp_fail += 1
            failures.append((status, t, detail))
            if show_lines:
                print(fmt_line(f"FAIL ({status})", t, ms))
                if detail:
                    for line in detail.splitlines():
                        print(f"  {line}")

    total = len(replays)
    if total > 1 or args.verbose:
        bits = [f"{ok} ok"]
        if lp_fail:    bits.append(f"{lp_fail} lp-fail")
        if emit_fail:  bits.append(f"{emit_fail} emit-fail")
        print(f"{total} replays: " + ", ".join(bits))

    sys.exit(0 if (lp_fail + emit_fail) == 0 else 1)


if __name__ == "__main__":
    main()
