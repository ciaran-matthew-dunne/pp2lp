#!/bin/bash
# Show PP rule coverage across the benchmark suite.
# Usage: bench/rule_coverage.sh [--by-suite] [--missing]
#
#   --by-suite   Break down by og/prv/synth
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

if $BY_SUITE; then
  # Collect per-suite
  OG_RULES=$(extract_rules bench/traces/*.replay | sort -u)
  PRV_RULES=$(extract_rules bench/prv/gen/replay/*.replay | sort -u)
  SYNTH_RULES=$(extract_rules bench/synth/but/gen/replay/*.replay | sort -u)

  printf "%-14s %3s %3s %3s\n" "RULE" "OG" "PRV" "SYN"
  printf "%-14s %3s %3s %3s\n" "----" "---" "---" "---"
  for rule in $ALL_RULES; do
    og=" "; prv=" "; syn=" "
    echo "$OG_RULES"   | grep -qx "$rule" && og="*"
    echo "$PRV_RULES"  | grep -qx "$rule" && prv="*"
    echo "$SYNTH_RULES" | grep -qx "$rule" && syn="*"
    if $MISSING && [ "$og$prv$syn" != "   " ]; then continue; fi
    printf "%-14s %3s %3s %3s\n" "$rule" "$og" "$prv" "$syn"
  done

  og_n=$(echo "$OG_RULES" | wc -w)
  prv_n=$(echo "$PRV_RULES" | wc -w)
  syn_n=$(echo "$SYNTH_RULES" | wc -w)
  all_covered=$(cat <(echo "$OG_RULES") <(echo "$PRV_RULES") <(echo "$SYNTH_RULES") | sort -u | wc -w)
  total=$(echo "$ALL_RULES" | wc -w)
  echo ""
  echo "Coverage: $all_covered/$total rules (og=$og_n, prv=$prv_n, synth=$syn_n)"
else
  # Simple: count occurrences across all replays
  ALL_REPLAY_RULES=$(extract_rules \
    bench/traces/*.replay \
    bench/prv/gen/replay/*.replay \
    bench/synth/but/gen/replay/*.replay)

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
