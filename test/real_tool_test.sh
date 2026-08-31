#!/usr/bin/env bash
set -euo pipefail

main_exe="$(realpath "$1")"
prelude="$(realpath "$2")"
list_library="$(realpath "$3")"
repo_root="$(cd "$(dirname "$main_exe")/../../../../" && pwd)"

skip_or_fail() {
  local message="$1"
  if [[ "${REQUIRE_REAL_TOOLS:-0}" == "1" ]]; then
    printf 'real-tool integration unavailable: %s\n' "$message" >&2
    exit 1
  fi
  printf 'SKIP real-tool integration: %s\n' "$message"
  exit 0
}

mypy_bin="${MYPY_BIN:-}"
if [[ -z "$mypy_bin" && -x "$repo_root/.venv/bin/mypy" ]]; then
  mypy_bin="$repo_root/.venv/bin/mypy"
fi
if [[ -z "$mypy_bin" && -n "$(command -v mypy || true)" ]]; then
  mypy_bin="$(command -v mypy)"
fi
if [[ -z "$mypy_bin" && -n "$(command -v uv || true)" ]]; then
  mypy_bin="$(cd "$repo_root" && uv run --frozen -- which mypy 2>/dev/null || true)"
fi
if [[ -z "$mypy_bin" || ! -x "$mypy_bin" ]]; then
  skip_or_fail "the pinned mypy executable was not found"
fi

dafny_bin="${DAFNY_BIN:-$(command -v dafny || true)}"
if [[ -z "$dafny_bin" || ! -x "$dafny_bin" ]]; then
  skip_or_fail "the pinned Dafny executable was not found"
fi

case "$($mypy_bin --version 2>&1)" in
  "mypy 1.18.2"*) ;;
  *) skip_or_fail "mypy is not version 1.18.2" ;;
esac
case "$($dafny_bin --version 2>&1)" in
  *"4.11.0"*) ;;
  *) skip_or_fail "Dafny is not version 4.11.0" ;;
esac

workdir="$(mktemp -d "${TMPDIR:-/tmp}/dafny-of-python-real-test.XXXXXX")"
trap 'rm -rf "$workdir"' EXIT

cat > "$workdir/program.py" <<'PYTHON'
def increment(x: int) -> int:
  return x + 1

assert increment(1) == 2
if exists k :: k == 0:
  pass
PYTHON

set +e
(
  cd "$workdir"
  "$main_exe" \
    --mypy "$mypy_bin" \
    --dafny "$dafny_bin" \
    --prelude "$prelude" \
    --list "$list_library" \
    --temp-root "$workdir" < program.py > output 2> errors
)
status=$?
set -e

test "$status" -eq 2
grep -q 'function increment' "$workdir/output"
grep -q 'exists k ::' "$workdir/output"
grep -q 'verifier finished with [0-9][0-9]* verified, 0 error' "$workdir/output"
grep -q 'Typechecking failed (exit code 2)' "$workdir/errors"

# A valid Python fixture must exercise the pinned mypy success path and the
# CLI's zero exit code while Dafny verifies the generated program.
cat > "$workdir/valid_program.py" <<'PYTHON'
def increment(x: int) -> int:
  return x + 1

assert increment(1) == 2
PYTHON

set +e
(
  cd "$workdir"
  "$main_exe" \
    --mypy "$mypy_bin" \
    --dafny "$dafny_bin" \
    --prelude "$prelude" \
    --list "$list_library" \
    --temp-root "$workdir" < valid_program.py > valid_output 2> valid_errors
)
status=$?
set -e

test "$status" -eq 0
grep -q 'function increment' "$workdir/valid_output"
grep -q 'verifier finished with [0-9][0-9]* verified, 0 error' "$workdir/valid_output"
# Dafny 4.11 reports harmless warnings (for example, an `old` expression that
# does not dereference the heap) on stderr. A zero exit code and a zero-error
# verifier summary are the validity checks; warnings are intentionally
# tolerated here.
