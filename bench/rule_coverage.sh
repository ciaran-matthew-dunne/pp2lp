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

# Per-suite replay globs. Each benchmark suite lives in bench/<name>/.
SUITES="claude prv og fuzz"
suite_glob() { echo "bench/$1/*.replay"; }

# Collect rules per suite (space-separated, unique)
declare -A SUITE_RULES
for s in $SUITES; do
  files=$(compgen -G "$(suite_glob "$s")" || true)
  if [ -n "$files" ]; then
    SUITE_RULES[$s]=$(extract_rules $files | sort -u)
  else
    SUITE_RULES[$s]=""
  fi
done

# Header abbreviation per suite (3 chars)
declare -A SUITE_HDR=([claude]="CLA" [prv]="PRV" [og]="OG " [fuzz]="FUZ")

if $BY_SUITE; then
  printf "%-14s" "RULE"
  for s in $SUITES; do printf " %4s" "${SUITE_HDR[$s]}"; done; echo
  printf "%-14s" "----"
  for s in $SUITES; do printf " %4s" "----"; done; echo

  for rule in $ALL_RULES; do
    any_hit=0
    line=$(printf "%-14s" "$rule")
    for s in $SUITES; do
      mark="-"
      if echo "${SUITE_RULES[$s]}" | grep -qx "$rule"; then mark="*"; any_hit=1; fi
      line="$line $(printf '%4s' "$mark")"
    done
    if $MISSING && [ "$any_hit" -eq 1 ]; then continue; fi
    echo "$line"
  done

  all_covered=""
  echo ""
  summary="Coverage:"
  for s in $SUITES; do
    n=$(echo "${SUITE_RULES[$s]}" | wc -w)
    summary="$summary $s=$n"
    all_covered="$all_covered ${SUITE_RULES[$s]}"
  done
  total=$(echo "$ALL_RULES" | wc -w)
  covered=$(echo "$all_covered" | tr ' ' '\n' | sort -u | grep -c .)
  echo "$summary total=$covered/$total"
else
  # Simple: count occurrences across all suites' replays
  ALL_FILES=""
  for s in $SUITES; do
    files=$(compgen -G "$(suite_glob "$s")" || true)
    ALL_FILES="$ALL_FILES $files"
  done
  ALL_REPLAY_RULES=$(extract_rules $ALL_FILES)

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

  covered=$(echo "$ALL_REPLAY_RULES" | sort -u | grep -c .)
  total=$(echo "$ALL_RULES" | wc -w)
  echo ""
  echo "Coverage: $covered/$total rules"
fi
