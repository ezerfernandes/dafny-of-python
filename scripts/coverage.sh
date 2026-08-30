#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

find . -type f -name '*.coverage' -delete
mkdir -p _coverage

BISECT_FILE="$ROOT_DIR/_coverage/bisect" \
  dune runtest --instrument-with bisect_ppx --force

# The prototype directories and the type-only AST module are deliberately not
# part of the maintained executable coverage scope. Keep exclusions explicit
# so adding another source directory to src/ cannot silently disappear.
REPORT_ARGS=(
  --coverage-path "$ROOT_DIR/_coverage"
  --expect src/
  --do-not-expect src/libs/parse/lexer.mll
  --do-not-expect src/libs/parse/menhir_parser.mly
  --do-not-expect src/libs/type/
  --do-not-expect src/libs/solver/
  --do-not-expect src/libs/transform/astdfy.ml
)

bisect-ppx-report html "${REPORT_ARGS[@]}" -o "$ROOT_DIR/_coverage/html"
SUMMARY="$(bisect-ppx-report summary "${REPORT_ARGS[@]}" --per-file)"
printf '%s\n' "$SUMMARY"
printf '%s\n' "$SUMMARY" | python3 "$ROOT_DIR/scripts/check_coverage.py"
