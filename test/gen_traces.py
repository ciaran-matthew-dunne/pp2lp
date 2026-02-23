#!/usr/bin/env python3
"""
Benchmark suite for PP (Predicate Prover) trace generation and replay.

This script processes .but proof goal files through two stages:
1. PP Stage: Generate proof traces from .but files
2. REPLAY Stage: Generate detailed replays from traces

USAGE
=====
Run from the directory containing .but files, or specify the directory:

    cd /path/to/test/smt
    python3 ../gen_traces.py .

Or from any location:

    python3 /path/to/gen_traces.py /path/to/directory/with/but/files

OUTPUT STRUCTURE
================
The script creates the following subdirectories in the target directory:

    target/
    ├── *.but              # Original proof goals (unchanged)
    ├── trace/             # .trace files from PP
    ├── replay/            # .replay files from REPLAY
    ├── replay-failures/   # Cases where PP succeeds but REPLAY fails
    │   ├── *.but          # Copy of original proof goal
    │   ├── *.trace        # Copy of trace from PP
    │   └── *.replay.goal  # Goal file for manual REPLAY testing
    └── misc/              # Files with no extension (if any)

REQUIREMENTS
============
- krt: Atelier B kernel runtime (must be in PATH or specify with --krt)
- PP.kin: PP bytecode (auto-detected or specify with --pp-kin)
- REPLAY.kin: REPLAY bytecode (auto-detected or specify with --replay-kin)

EXAMPLES
========
    # Basic run with default timeouts (60s PP, 120s REPLAY)
    python3 gen_traces.py .

    # 30 second timeout for both stages
    python3 gen_traces.py -t 30 .

    # Clean output directories first, then run
    python3 gen_traces.py --clean .

    # Generate JSON report
    python3 gen_traces.py --json results.json .

    # Quiet mode (summary only)
    python3 gen_traces.py -q .

    # Analyze failures only (skip processing)
    python3 gen_traces.py --analyze-only .

    # Convert .but files to .goal files with TraceOn flag (no execution)
    python3 gen_traces.py --convert-only .
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from collections import defaultdict
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Optional

# =============================================================================
# Data Classes
# =============================================================================

@dataclass
class StageResult:
    """Result of a single stage (PP or REPLAY)."""
    success: bool
    elapsed_seconds: float
    timeout: bool = False
    error: Optional[str] = None
    output_size: int = 0


@dataclass
class FileResult:
    """Result of processing a single .but file."""
    filename: str
    pp: Optional[StageResult] = None
    replay: Optional[StageResult] = None
    result: str = "UNKNOWN"  # SUCCES, INTERUPTION, etc.

    @property
    def total_time(self) -> float:
        t = 0.0
        if self.pp:
            t += self.pp.elapsed_seconds
        if self.replay:
            t += self.replay.elapsed_seconds
        return t


@dataclass
class BenchmarkResults:
    """Aggregate benchmark results."""
    files: list[FileResult] = field(default_factory=list)
    pp_timeout: float = 60.0
    replay_timeout: float = 120.0

    @property
    def total_files(self) -> int:
        return len(self.files)

    @property
    def pp_succeeded(self) -> int:
        return sum(1 for f in self.files if f.pp and f.pp.success)

    @property
    def pp_failed(self) -> int:
        return sum(1 for f in self.files if f.pp and not f.pp.success)

    @property
    def pp_timeouts(self) -> int:
        return sum(1 for f in self.files if f.pp and f.pp.timeout)

    @property
    def replay_succeeded(self) -> int:
        return sum(1 for f in self.files if f.replay and f.replay.success)

    @property
    def replay_failed(self) -> int:
        return sum(1 for f in self.files if f.replay and not f.replay.success)

    @property
    def replay_timeouts(self) -> int:
        return sum(1 for f in self.files if f.replay and f.replay.timeout)

    @property
    def total_pp_time(self) -> float:
        return sum(f.pp.elapsed_seconds for f in self.files if f.pp)

    @property
    def total_replay_time(self) -> float:
        return sum(f.replay.elapsed_seconds for f in self.files if f.replay)

    @property
    def total_time(self) -> float:
        return self.total_pp_time + self.total_replay_time

    def to_dict(self) -> dict:
        return {
            "summary": {
                "total_files": self.total_files,
                "pp_timeout_seconds": self.pp_timeout,
                "replay_timeout_seconds": self.replay_timeout,
                "pp": {
                    "succeeded": self.pp_succeeded,
                    "failed": self.pp_failed,
                    "timeouts": self.pp_timeouts,
                    "total_time_seconds": round(self.total_pp_time, 3),
                },
                "replay": {
                    "succeeded": self.replay_succeeded,
                    "failed": self.replay_failed,
                    "timeouts": self.replay_timeouts,
                    "total_time_seconds": round(self.total_replay_time, 3),
                },
                "total_time_seconds": round(self.total_time, 3),
            },
            "files": [
                {
                    "filename": f.filename,
                    "result": f.result,
                    "pp": asdict(f.pp) if f.pp else None,
                    "replay": asdict(f.replay) if f.replay else None,
                    "total_time_seconds": round(f.total_time, 3),
                }
                for f in self.files
            ]
        }


@dataclass
class OutputDirs:
    """Output directory paths."""
    base: Path
    trace: Path
    replay: Path
    replay_failures: Path
    misc: Path

    @classmethod
    def create(cls, base_dir: Path) -> "OutputDirs":
        """Create output directories under base_dir."""
        dirs = cls(
            base=base_dir,
            trace=base_dir / "trace",
            replay=base_dir / "replay",
            replay_failures=base_dir / "replay-failures",
            misc=base_dir / "misc",
        )
        dirs.trace.mkdir(exist_ok=True)
        dirs.replay.mkdir(exist_ok=True)
        dirs.replay_failures.mkdir(exist_ok=True)
        dirs.misc.mkdir(exist_ok=True)
        return dirs


# =============================================================================
# Tool Discovery
# =============================================================================

def find_krt() -> Optional[str]:
    """Find krt binary."""
    result = subprocess.run(["which", "krt"], capture_output=True, text=True)
    if result.returncode == 0:
        return result.stdout.strip()
    for path in ["/opt/atelierb-free-24.04.2/bin/krt", "/usr/local/bin/krt"]:
        if os.path.exists(path):
            return path
    return None


def find_pp_kin() -> Optional[str]:
    """Find PP.kin bytecode."""
    for path in [
        "/opt/atelierb-free-24.04.2/bin/PP.kin",
        os.path.expanduser("~/atelierb/bin/PP.kin"),
    ]:
        if os.path.exists(path):
            return path
    return None


def find_replay_kin() -> Optional[str]:
    """Find REPLAY.kin bytecode."""
    script_dir = Path(__file__).parent.parent
    for path in [
        script_dir / "atelierb/tools/linux_x64/REPLAY.kin",
        script_dir / "atelierb/tools/macosx/REPLAY.kin",
        Path("/opt/atelierb-free-24.04.2/bin/REPLAY.kin"),
    ]:
        if path.exists():
            return str(path)
    return None


# =============================================================================
# File Conversion Utilities
# =============================================================================

def convert_but_to_goal(but_content: str, trace_filename: str, res_filename: str) -> str:
    """
    Convert a .but file content to a .goal file with TraceOn flag.

    .but format: Flag(TypeOn("...")) & Flag(FileOn("...res")) & Set(...)
    .goal format: Flag(TraceOn("...trace")) & Flag(FileOn("...res")) & Set(...)
    """
    content = re.sub(r'Flag\(TypeOn\([^)]+\)\)\s*&\s*', '', but_content)
    if 'Flag(FileOn(' in content:
        content = re.sub(
            r'Flag\(FileOn\("([^"]+)"\)\)',
            f'Flag(TraceOn("{trace_filename}")) & Flag(FileOn("{res_filename}"))',
            content
        )
    else:
        content = f'Flag(TraceOn("{trace_filename}")) & Flag(FileOn("{res_filename}")) & {content}'
    return content


def create_replay_goal(trace_filename: str, replay_res_filename: str) -> str:
    """Create a replay goal file content."""
    return f'Flag(FileOn("{replay_res_filename}")) & ("{trace_filename}")'


# =============================================================================
# Execution Utilities
# =============================================================================

def run_krt_timed(
    krt_path: str,
    kin_path: str,
    goal_file: str,
    cwd: str,
    timeout: float,
    capture_stdout: bool = False
) -> tuple[StageResult, Optional[str]]:
    """
    Run krt with timing and return (StageResult, stdout_if_captured).
    """
    start_time = time.perf_counter()
    stdout_content = None

    try:
        result = subprocess.run(
            [krt_path, "-b", kin_path, goal_file],
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=timeout
        )
        elapsed = time.perf_counter() - start_time
        success = result.returncode == 0

        if capture_stdout and result.stdout:
            stdout_content = result.stdout

        error_msg = None
        if result.stderr:
            error_msg = result.stderr.strip()[:200]
        if result.stdout and not success:
            # Some errors go to stdout
            error_msg = result.stdout.strip()[:200]

        return StageResult(
            success=success,
            elapsed_seconds=elapsed,
            timeout=False,
            error=error_msg if not success else None,
            output_size=len(result.stdout) if result.stdout else 0
        ), stdout_content

    except subprocess.TimeoutExpired:
        elapsed = time.perf_counter() - start_time
        return StageResult(
            success=False,
            elapsed_seconds=elapsed,
            timeout=True,
            error=f"Timeout after {timeout}s"
        ), None

    except Exception as e:
        elapsed = time.perf_counter() - start_time
        return StageResult(
            success=False,
            elapsed_seconds=elapsed,
            timeout=False,
            error=str(e)[:200]
        ), None


def move_to_output_dir(src: Path, output_dirs: OutputDirs) -> Optional[Path]:
    """
    Move a file to the appropriate output directory based on its extension.
    Returns the new path, or None if file doesn't exist.
    """
    if not src.exists():
        return None

    suffix = src.suffix.lower()

    if suffix == ".trace":
        dest_dir = output_dirs.trace
    elif suffix == ".replay":
        dest_dir = output_dirs.replay
    elif suffix == "":
        dest_dir = output_dirs.misc
    else:
        return src

    dest = dest_dir / src.name
    shutil.move(str(src), str(dest))
    return dest


# =============================================================================
# Convert Only Mode
# =============================================================================

def convert_but_files_only(
    but_files: list[Path],
    output_dir: Path,
    quiet: bool = False
) -> int:
    """
    Convert .but files to .goal files with TraceOn flag.

    Returns number of files converted.
    """
    goal_dir = output_dir / "goal"
    goal_dir.mkdir(exist_ok=True)

    count = 0
    for but_file in but_files:
        stem = but_file.stem
        but_content = but_file.read_text()

        # Convert to goal format with TraceOn
        goal_content = convert_but_to_goal(but_content, f"{stem}.trace", f"{stem}.res")

        # Write to goal directory
        goal_file = goal_dir / f"{stem}.goal"
        goal_file.write_text(goal_content)
        count += 1

        if not quiet:
            print(f"Converted: {but_file.name} -> goal/{stem}.goal")

    return count


# =============================================================================
# Main Processing
# =============================================================================

def process_but_file(
    but_file: Path,
    krt: str,
    pp_kin: str,
    replay_kin: str,
    pp_timeout: float,
    replay_timeout: float,
    output_dirs: OutputDirs,
    verbose: bool = False
) -> FileResult:
    """Process a single .but file to generate trace and replay with timing."""
    stem = but_file.stem
    directory = but_file.parent

    file_result = FileResult(filename=str(but_file.name))

    # Working filenames (in source directory during processing)
    goal_file = directory / f"{stem}.goal"
    trace_file = directory / f"{stem}.trace"
    res_file = directory / f"{stem}.res"
    replay_goal_file = directory / f"{stem}.replay.goal"
    replay_file = directory / f"{stem}.replay"
    replay_res_file = directory / f"{stem}.replay.res"

    # Read .but file
    but_content = but_file.read_text()

    # Step 1: Create .goal file with TraceOn
    goal_content = convert_but_to_goal(but_content, f"{stem}.trace", f"{stem}.res")
    goal_file.write_text(goal_content)

    # Step 2: Run PP to generate trace
    pp_result, _ = run_krt_timed(
        krt, pp_kin, str(goal_file.name), str(directory), pp_timeout
    )
    file_result.pp = pp_result

    # Check if trace was generated
    if not trace_file.exists() or trace_file.stat().st_size == 0:
        pp_result.success = False
        if not pp_result.error:
            pp_result.error = "No trace generated"

    # Read result
    if res_file.exists():
        file_result.result = res_file.read_text().strip().replace('\ufeff', '')

    # Update output size
    if trace_file.exists():
        pp_result.output_size = trace_file.stat().st_size

    # Cleanup .goal file (keep .res file)
    goal_file.unlink(missing_ok=True)

    if not pp_result.success:
        if verbose:
            print(f"  PP failed: {pp_result.error}")
        trace_file.unlink(missing_ok=True)
        return file_result

    # Move trace file to output directory
    move_to_output_dir(trace_file, output_dirs)

    # Step 3: Create replay goal file (referencing trace in output dir)
    trace_in_output = output_dirs.trace / f"{stem}.trace"
    replay_goal_content = create_replay_goal(str(trace_in_output), f"{stem}.replay.res")
    replay_goal_file.write_text(replay_goal_content)

    # Step 4: Run REPLAY to generate replay trace
    replay_result, stdout = run_krt_timed(
        krt, replay_kin, str(replay_goal_file.name), str(directory),
        replay_timeout, capture_stdout=True
    )
    file_result.replay = replay_result

    if stdout and len(stdout) > 10:  # More than just whitespace
        replay_file.write_text(stdout)
        replay_result.output_size = len(stdout)
        replay_result.success = True
        move_to_output_dir(replay_file, output_dirs)
    else:
        replay_result.success = False
        if not replay_result.error:
            replay_result.error = "No replay output"

    # Cleanup intermediate files
    replay_goal_file.unlink(missing_ok=True)
    replay_res_file.unlink(missing_ok=True)
    replay_file.unlink(missing_ok=True)

    # Move any files without extensions to misc
    for f in directory.glob(f"{stem}"):
        if f.is_file() and f.suffix == "":
            move_to_output_dir(f, output_dirs)

    return file_result


# =============================================================================
# Failure Analysis
# =============================================================================

def get_trace_stats(trace_path: Path) -> dict:
    """Get statistics about a trace file."""
    content = trace_path.read_text()
    lines = content.strip().split('\n')

    rules = defaultdict(int)
    for line in lines:
        line = line.strip()
        if line.startswith('[') and ']' in line:
            rule = line[1:line.index(']')]
            if '(' in rule:
                base_rule = rule[:rule.index('(')]
            else:
                base_rule = rule
            rules[base_rule] += 1

    return {
        'size_bytes': trace_path.stat().st_size,
        'num_lines': len(lines),
        'num_rules': sum(rules.values()),
        'unique_rules': len(rules),
        'top_rules': sorted(rules.items(), key=lambda x: -x[1])[:5],
    }


def categorize_replay_error(error: Optional[str], trace_size: int) -> str:
    """Categorize a REPLAY error."""
    if not error:
        if trace_size <= 10:
            return "EMPTY_TRACE"
        return "NO_OUTPUT"
    if "GOALS STACK OVERFLOW" in error:
        return "STACK_OVERFLOW"
    if "missing atomic symbol" in error:
        return "PARSE_ERROR"
    if "Timeout" in error:
        return "TIMEOUT"
    return "OTHER"


def create_replay_failures_dir(
    results: BenchmarkResults,
    output_dirs: OutputDirs,
    source_dir: Path
) -> dict:
    """
    Create replay-failures directory with files for cases where PP succeeded
    but REPLAY failed.

    Returns statistics about the failures.
    """
    # Clear existing replay-failures
    for f in output_dirs.replay_failures.iterdir():
        if f.is_file():
            f.unlink()

    failure_stats = defaultdict(list)

    for file_result in results.files:
        # Only interested in cases where PP succeeded but REPLAY failed
        if not (file_result.pp and file_result.pp.success):
            continue
        if file_result.replay and file_result.replay.success:
            continue

        stem = file_result.filename.replace('.but', '')
        trace_path = output_dirs.trace / f"{stem}.trace"
        but_path = source_dir / file_result.filename

        if not trace_path.exists():
            continue

        # Categorize the error
        trace_size = trace_path.stat().st_size
        error = file_result.replay.error if file_result.replay else None
        category = categorize_replay_error(error, trace_size)

        failure_stats[category].append({
            'name': stem,
            'trace_size': trace_size,
            'error': error,
        })

        # Copy files to replay-failures
        if but_path.exists():
            shutil.copy(but_path, output_dirs.replay_failures / but_path.name)
        shutil.copy(trace_path, output_dirs.replay_failures / trace_path.name)

        # Create replay.goal file
        replay_goal_content = f'Flag(FileOn("{stem}.replay.res")) & ("{stem}.trace")'
        (output_dirs.replay_failures / f"{stem}.replay.goal").write_text(replay_goal_content)

    return dict(failure_stats)


def print_failure_analysis(
    failure_stats: dict,
    output_dirs: OutputDirs,
    verbose: bool = False
):
    """Print detailed failure analysis."""
    if not failure_stats:
        print("\nNo REPLAY failures to analyze.")
        return

    total_failures = sum(len(v) for v in failure_stats.values())

    print()
    print("=" * 60)
    print("REPLAY FAILURE ANALYSIS")
    print("=" * 60)
    print(f"\nTotal failures: {total_failures}")
    print(f"Files copied to: {output_dirs.replay_failures}/")
    print()

    print("-" * 60)
    print("FAILURE CATEGORIES")
    print("-" * 60)

    category_descriptions = {
        'STACK_OVERFLOW': 'REPLAY stack overflow (proof too deep/complex)',
        'EMPTY_TRACE': 'Empty trace (PP did not complete proof)',
        'PARSE_ERROR': 'Trace parse error (malformed trace)',
        'TIMEOUT': 'REPLAY timeout',
        'NO_OUTPUT': 'No output from REPLAY',
        'OTHER': 'Other errors',
    }

    for category in ['STACK_OVERFLOW', 'EMPTY_TRACE', 'PARSE_ERROR', 'TIMEOUT', 'NO_OUTPUT', 'OTHER']:
        if category not in failure_stats:
            continue

        failures = failure_stats[category]
        desc = category_descriptions.get(category, category)
        print(f"\n{category} ({len(failures)} cases): {desc}")

        if verbose:
            for f in failures:
                size_str = f"{f['trace_size']:,} bytes" if f['trace_size'] > 10 else "empty"
                print(f"  - {f['name']} ({size_str})")
        else:
            for f in failures[:3]:
                size_str = f"{f['trace_size']:,} bytes" if f['trace_size'] > 10 else "empty"
                print(f"  - {f['name']} ({size_str})")
            if len(failures) > 3:
                print(f"  ... and {len(failures) - 3} more")

    # Statistics for stack overflow cases
    stack_overflow = failure_stats.get('STACK_OVERFLOW', [])
    if stack_overflow:
        sizes = [f['trace_size'] for f in stack_overflow]
        print()
        print("-" * 60)
        print("STACK OVERFLOW STATISTICS")
        print("-" * 60)
        print(f"  Count: {len(sizes)}")
        print(f"  Trace sizes: {min(sizes):,} - {max(sizes):,} bytes")
        print(f"  Average: {sum(sizes)//len(sizes):,} bytes")

    print()
    print("-" * 60)
    print("TO TEST A FAILURE MANUALLY:")
    print("-" * 60)
    print(f"  cd {output_dirs.replay_failures}")
    print("  krt -b /opt/atelierb-free-24.04.2/bin/REPLAY.kin <name>.replay.goal")
    print()


def analyze_existing_failures(output_dirs: OutputDirs, krt: str, replay_kin: str):
    """Analyze existing replay-failures directory."""
    if not output_dirs.replay_failures.exists():
        print("No replay-failures directory found.")
        return

    goal_files = sorted(output_dirs.replay_failures.glob("*.replay.goal"))
    if not goal_files:
        print("No .replay.goal files found in replay-failures/")
        return

    print("=" * 60)
    print("REPLAY FAILURE ANALYSIS")
    print("=" * 60)
    print(f"\nAnalyzing {len(goal_files)} cases in {output_dirs.replay_failures}/\n")

    failure_stats = defaultdict(list)

    for goal_file in goal_files:
        stem = goal_file.stem.replace('.replay', '')
        trace_file = output_dirs.replay_failures / f"{stem}.trace"

        trace_size = trace_file.stat().st_size if trace_file.exists() else 0

        # Run REPLAY to get actual error
        try:
            result = subprocess.run(
                [krt, "-b", replay_kin, goal_file.name],
                cwd=str(output_dirs.replay_failures),
                capture_output=True,
                text=True,
                timeout=30
            )
            error = (result.stdout + result.stderr).strip()[:200]
            success = result.returncode == 0 and len(result.stdout) > 100
        except subprocess.TimeoutExpired:
            error = "Timeout"
            success = False
        except Exception as e:
            error = str(e)
            success = False

        if success:
            continue  # Skip if it actually succeeded

        category = categorize_replay_error(error, trace_size)

        stats = {'name': stem, 'trace_size': trace_size, 'error': error}
        if trace_file.exists() and trace_size > 10:
            stats['trace_stats'] = get_trace_stats(trace_file)

        failure_stats[category].append(stats)

    # Print results
    print_failure_analysis(dict(failure_stats), output_dirs, verbose=True)


# =============================================================================
# Output Formatting
# =============================================================================

def format_time(seconds: float) -> str:
    """Format time in human-readable format."""
    if seconds < 0.001:
        return f"{seconds*1000000:.0f}us"
    elif seconds < 1:
        return f"{seconds*1000:.1f}ms"
    elif seconds < 60:
        return f"{seconds:.2f}s"
    else:
        minutes = int(seconds // 60)
        secs = seconds % 60
        return f"{minutes}m{secs:.1f}s"


def print_summary(results: BenchmarkResults, output_dirs: OutputDirs):
    """Print benchmark summary."""
    print()
    print("=" * 60)
    print("BENCHMARK SUMMARY")
    print("=" * 60)
    print()
    print(f"Total files processed: {results.total_files}")
    print(f"Timeouts: PP={results.pp_timeout}s, REPLAY={results.replay_timeout}s")
    print()
    print("PP Stage:")
    print(f"  Succeeded: {results.pp_succeeded}")
    print(f"  Failed:    {results.pp_failed}")
    print(f"  Timeouts:  {results.pp_timeouts}")
    print(f"  Total time: {format_time(results.total_pp_time)}")
    if results.pp_succeeded > 0:
        avg_pp = results.total_pp_time / results.pp_succeeded
        print(f"  Avg time (success): {format_time(avg_pp)}")
    print()
    print("REPLAY Stage:")
    print(f"  Succeeded: {results.replay_succeeded}")
    print(f"  Failed:    {results.replay_failed}")
    print(f"  Timeouts:  {results.replay_timeouts}")
    print(f"  Total time: {format_time(results.total_replay_time)}")
    if results.replay_succeeded > 0:
        avg_replay = results.total_replay_time / results.replay_succeeded
        print(f"  Avg time (success): {format_time(avg_replay)}")
    print()
    print(f"Total time: {format_time(results.total_time)}")
    print()
    print("Output directories:")
    print(f"  Traces:          {output_dirs.trace}/")
    print(f"  Replays:         {output_dirs.replay}/")
    print(f"  Replay failures: {output_dirs.replay_failures}/")
    print("=" * 60)


def cleanup_old_outputs(output_dirs: OutputDirs, quiet: bool = False):
    """Remove old output files from output directories."""
    count = 0
    for d in [output_dirs.trace, output_dirs.replay, output_dirs.replay_failures, output_dirs.misc]:
        if d.exists():
            for f in d.iterdir():
                if f.is_file():
                    f.unlink()
                    count += 1
    if not quiet and count > 0:
        print(f"Cleaned up {count} old output files")


# =============================================================================
# Main Entry Point
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Benchmark suite for PP trace generation and replay",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Output structure:
  trace/           .trace files from PP
  replay/          .replay files from REPLAY
  replay-failures/ Cases where PP succeeds but REPLAY fails
  misc/            Files with no extension

Examples:
  %(prog)s .                        Process current directory
  %(prog)s -t 30 .                  30 second timeout for both stages
  %(prog)s --clean .                Clean and reprocess
  %(prog)s --analyze-only .         Only analyze existing failures
  %(prog)s -v --json results.json . Verbose with JSON output
        """
    )
    parser.add_argument("directory", nargs="?", default=".",
                        help="Directory containing .but files")
    parser.add_argument("--pp-kin", help="Path to PP.kin")
    parser.add_argument("--replay-kin", help="Path to REPLAY.kin")
    parser.add_argument("--krt", help="Path to krt binary")
    parser.add_argument("-t", "--timeout", type=float, default=None,
                        help="Timeout in seconds for both stages")
    parser.add_argument("--pp-timeout", type=float, default=60.0,
                        help="Timeout for PP stage (default: 60s)")
    parser.add_argument("--replay-timeout", type=float, default=120.0,
                        help="Timeout for REPLAY stage (default: 120s)")
    parser.add_argument("-v", "--verbose", action="store_true",
                        help="Verbose output")
    parser.add_argument("--json", metavar="FILE",
                        help="Write detailed results to JSON file")
    parser.add_argument("-q", "--quiet", action="store_true",
                        help="Minimal output (summary only)")
    parser.add_argument("--clean", action="store_true",
                        help="Clean output directories before processing")
    parser.add_argument("-o", "--output-dir", metavar="DIR",
                        help="Base directory for output (default: same as input)")
    parser.add_argument("--analyze-only", action="store_true",
                        help="Only analyze existing replay-failures (skip processing)")
    parser.add_argument("--convert-only", action="store_true",
                        help="Only convert .but files to .goal files with TraceOn flag (no execution)")
    args = parser.parse_args()

    # Handle unified timeout option
    pp_timeout = args.timeout if args.timeout else args.pp_timeout
    replay_timeout = args.timeout if args.timeout else args.replay_timeout

    # Find tools
    krt = args.krt or find_krt()
    pp_kin = args.pp_kin or find_pp_kin()
    replay_kin = args.replay_kin or find_replay_kin()

    # Setup directories
    directory = Path(args.directory).resolve()
    output_base = Path(args.output_dir).resolve() if args.output_dir else directory

    # Convert-only mode (doesn't need krt or kin files)
    if args.convert_only:
        # Find .but files
        but_files = sorted(directory.glob("**/*.but"))
        if not but_files:
            print(f"No .but files found in {directory}")
            sys.exit(1)

        if not args.quiet:
            print(f"Found {len(but_files)} .but files")
            print(f"Output: {output_base}/goal/")
            print()

        count = convert_but_files_only(but_files, output_base, args.quiet)

        if not args.quiet:
            print()
            print(f"Converted {count} .but files to .goal files in {output_base}/goal/")
        return

    if not krt:
        print("Error: krt not found. Use --krt to specify path.", file=sys.stderr)
        sys.exit(1)
    if not pp_kin and not args.analyze_only:
        print("Error: PP.kin not found. Use --pp-kin to specify path.", file=sys.stderr)
        sys.exit(1)
    if not replay_kin:
        print("Error: REPLAY.kin not found. Use --replay-kin to specify path.", file=sys.stderr)
        sys.exit(1)

    output_dirs = OutputDirs.create(output_base)

    # Analyze-only mode
    if args.analyze_only:
        analyze_existing_failures(output_dirs, krt, replay_kin)
        return

    if not args.quiet:
        print(f"Using krt: {krt}")
        print(f"Using PP.kin: {pp_kin}")
        print(f"Using REPLAY.kin: {replay_kin}")
        print(f"Timeouts: PP={pp_timeout}s, REPLAY={replay_timeout}s")
        print(f"Output: {output_base}/")
        print()

    # Clean old outputs if requested
    if args.clean:
        cleanup_old_outputs(output_dirs, args.quiet)
        if not args.quiet:
            print()

    # Find .but files (exclude output directories)
    but_files = []
    exclude_dirs = {output_dirs.trace, output_dirs.replay, output_dirs.replay_failures, output_dirs.misc}
    for f in sorted(directory.glob("**/*.but")):
        skip = False
        for excl in exclude_dirs:
            try:
                f.relative_to(excl)
                skip = True
                break
            except ValueError:
                pass
        if not skip:
            but_files.append(f)

    if not but_files:
        print(f"No .but files found in {directory}")
        sys.exit(1)

    if not args.quiet:
        print(f"Found {len(but_files)} .but files")
        print()

    # Initialize results
    results = BenchmarkResults(
        pp_timeout=pp_timeout,
        replay_timeout=replay_timeout
    )

    # Process files
    for but_file in but_files:
        rel_path = but_file.relative_to(directory) if but_file.is_relative_to(directory) else but_file

        if not args.quiet:
            print(f"Processing {rel_path}...", end=" ", flush=True)

        file_result = process_but_file(
            but_file, krt, pp_kin, replay_kin,
            pp_timeout, replay_timeout, output_dirs, args.verbose
        )
        results.files.append(file_result)

        if not args.quiet:
            pp_status = "OK" if file_result.pp and file_result.pp.success else "FAIL"
            pp_time = format_time(file_result.pp.elapsed_seconds) if file_result.pp else "-"
            if file_result.pp and file_result.pp.timeout:
                pp_status = "TIMEOUT"

            replay_status = "-"
            replay_time = "-"
            if file_result.replay:
                replay_status = "OK" if file_result.replay.success else "FAIL"
                replay_time = format_time(file_result.replay.elapsed_seconds)
                if file_result.replay.timeout:
                    replay_status = "TIMEOUT"

            print(f"PP:{pp_status}({pp_time}) REPLAY:{replay_status}({replay_time}) [{file_result.result}]")

    # Print summary
    print_summary(results, output_dirs)

    # Create replay-failures directory and analyze
    failure_stats = create_replay_failures_dir(results, output_dirs, directory)
    print_failure_analysis(failure_stats, output_dirs, args.verbose)

    # Write JSON results if requested
    if args.json:
        json_data = results.to_dict()
        json_data['failure_analysis'] = {
            cat: [{'name': f['name'], 'trace_size': f['trace_size']} for f in failures]
            for cat, failures in failure_stats.items()
        }
        with open(args.json, 'w') as f:
            json.dump(json_data, f, indent=2)
        print(f"Detailed results written to: {args.json}")


if __name__ == "__main__":
    main()
