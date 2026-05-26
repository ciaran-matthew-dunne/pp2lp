#!/bin/sh
# PostToolUse hook for Edit/Write/MultiEdit.
#
# Reads the tool-call JSON on stdin, inspects the edited path, and:
#   - rebuilds the OCaml binary after edits under ocaml/
#   - clears stale *.lpo after edits under lp/
#
# Hook exit code surfaces to Claude — non-zero on rebuild failure is
# intentional, so a broken build is visible immediately.

set -eu

ROOT=${CLAUDE_PROJECT_DIR:-/home/ciaran/prog/pp2lp}

path=$(jq -r '.tool_input.file_path // empty' 2>/dev/null || echo "")
[ -z "$path" ] && exit 0

case "$path" in
  "$ROOT"/ocaml/*)
    dune build --root "$ROOT/ocaml" 2>&1
    ;;
  "$ROOT"/lp/*)
    find "$ROOT/lp" -name '*.lpo' -delete 2>/dev/null || true
    ;;
esac
