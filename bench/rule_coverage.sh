#!/bin/bash
# Show PP rule coverage across the benchmark suite.
# Usage: bench/rule_coverage.sh [--by-suite] [--missing]
#
#   --by-suite   Break down by archive (og+prv) vs synth
#   --missing    Show only rules with zero coverage

set -euo pipefail
cd "$(dirname "$0")/.."

BY_SUITE=false
MISSING=false
for arg in "$@"; do
  case "$arg" in
    --by-suite) BY_SUITE=true ;;
    --missing)  MISSING=true ;;
    *)          echo "Unknown option: $arg"; exit 1 ;;
  esac
done

# All rules from rule_db.ml (arity table keys)
ALL_RULES=$(grep -oP '"[A-Z][A-Z0-9_]+"' ocaml/src/rule_db.ml | tr -d '"' | sort -u)

# Extract rule names from replay files, stripping args and _1 suffixes
extract_rules() {
  sed 's/\].*//' "$@" 2>/dev/null | sed 's/\[//' | sed 's/(.*//; s/_1$//' | grep -E '^[A-Z]' || true
}

# Current replays
SYNTH_GLOB="bench/gen/*.replay"
# Archived replays (og traces + prv)
ARCHIVE_GLOB="bench/archive/traces/*.replay bench/archive/prv/gen/replay/*.replay"

if $BY_SUITE; then
  ARCHIVE_RULES=$(extract_rules $ARCHIVE_GLOB | sort -u)
  SYNTH_RULES=$(extract_rules $SYNTH_GLOB | sort -u)

  printf "%-14s %4s %4s\n" "RULE" "ARC" "SYN"
  printf "%-14s %4s %4s\n" "----" "----" "----"
  for rule in $ALL_RULES; do
    arc=" "; syn=" "
    echo "$ARCHIVE_RULES" | grep -qx "$rule" && arc="*"
    echo "$SYNTH_RULES"   | grep -qx "$rule" && syn="*"
    if $MISSING && [ "$arc$syn" != "  " ]; then continue; fi
    printf "%-14s %4s %4s\n" "$rule" "$arc" "$syn"
  done

  arc_n=$(echo "$ARCHIVE_RULES" | wc -w)
  syn_n=$(echo "$SYNTH_RULES" | wc -w)
  all_covered=$(cat <(echo "$ARCHIVE_RULES") <(echo "$SYNTH_RULES") | sort -u | wc -w)
  total=$(echo "$ALL_RULES" | wc -w)
  echo ""
  echo "Coverage: $all_covered/$total rules (archive=$arc_n, synth=$syn_n)"
else
  # Simple: count occurrences across all replays
  ALL_REPLAY_RULES=$(extract_rules $SYNTH_GLOB $ARCHIVE_GLOB)

  if $MISSING; then
    covered=$(echo "$ALL_REPLAY_RULES" | sort -u)
    echo "Rules with no coverage:"
    for rule in $ALL_RULES; do
      echo "$covered" | grep -qx "$rule" || echo "  $rule"
    done
  else
    printf "%-14s %6s\n" "RULE" "COUNT"
    printf "%-14s %6s\n" "----" "-----"
    for rule in $ALL_RULES; do
      n=$(echo "$ALL_REPLAY_RULES" | grep -cx "$rule")
      printf "%-14s %6d\n" "$rule" "$n"
    done
  fi

  covered=$(echo "$ALL_REPLAY_RULES" | sort -u | wc -w)
  total=$(echo "$ALL_RULES" | wc -w)
  echo ""
  echo "Coverage: $covered/$total rules"
fi
