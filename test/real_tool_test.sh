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
# pre len(xs) > 0
def first(xs: list[int]) -> int:
  return xs[0]

# pre len(xs) > 1
def tail(xs: list[int]) -> list[int]:
  return xs[1:]

# pre len(xs) > 1
def tail_caller(xs: list[int]) -> list[int]:
  return tail(xs)

def mutate(xs: list[int]) -> None:
  xs.append(2)

def alias_mutate(xs: list[int]) -> None:
  ys = xs
  ys.append(2)

def branch_alias_mutate(xs: list[int], flag: bool) -> None:
  if flag:
    ys = xs
    ys.append(2)

def alias_lookup(mapping: dict[int, int], key: int) -> int:
  alias = mapping
  if key in alias:
    return mapping[key]
  else:
    return 0

def alias_literal_lookup() -> int:
  mapping: dict[int, int] = {1: 2}
  alias = mapping
  return alias[1]

def loop_entry_environment(other: list[int], mapping: list[int]) -> None:
  for key in other:
    assert key == key

def increment(x: int) -> int:
  return x + 1

def method_form(x: int) -> int:
  y = x + 1
  return y

def ordered(a: int, b: int, c: int) -> bool:
  return a < b < c

# pre value in xs
def contains(xs: list[int], value: int) -> bool:
  return value in xs

def choose(x: int) -> int:
  if x == 0:
    return 0
  elif [1][0] == 1:
    return 1
  else:
    return 2

def repeat_guard(x: int) -> None:
  while [1][0] == x:
    break

assert first([1]) == 1
tail_result = tail([1, 2])
tail_caller_result = tail_caller([1, 2])
assert increment(1) == 2
method_result = method_form(1)
assert ordered(1, 2, 3)
assert contains([1], 1)
chosen = choose(0)
singleton_parenthesized = (1,)
singleton_trailing = 2,

empty_list: list[int] = []
assert len(empty_list) == 0

values: set[int] = {1, 2}
other_values: set[int] = {2, 3}
empty_values: set[int] = set()
from_list: set[int] = set([1, 2])
assert len(empty_values) == 0
assert empty_values == set()
union: set[int] = values | other_values
intersection: set[int] = union & other_values
difference: set[int] = union - other_values
assert 3 in union
assert 2 in intersection
assert 1 in difference

mapping: dict[int, int] = {1: 10, 1: 11}
empty_mapping: dict[int, int] = dict()
assert len(empty_mapping) == 0
assert empty_mapping == dict()
assert mapping[1] == 11
mapping[1] = 12
assert mapping[1] == 12

key = 1
if key in mapping:
  assert mapping[key] == 12

# pre key in mapping
def lookup(mapping: dict[int, int], key: int) -> int:
  return mapping[key]

assert lookup(mapping, 1) == 12
alias_result = alias_lookup(mapping, 1)
literal_alias_result = alias_literal_lookup()

for item in values:
  assert item in values

for key in mapping:
  assert key in mapping

loop_items: list[int] = [1]
for loop_item in loop_items:
  continue

mutate(loop_items)
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
grep -q 'function first' "$workdir/valid_output"
grep -q 'method tail' "$workdir/valid_output"
grep -q 'method tail_caller' "$workdir/valid_output"
grep -q 'rangeLower' "$workdir/valid_output"
grep -q 'method mutate' "$workdir/valid_output"
grep -q 'method alias_mutate' "$workdir/valid_output"
grep -q 'method branch_alias_mutate' "$workdir/valid_output"
grep -q 'method alias_lookup' "$workdir/valid_output"
grep -q 'method alias_literal_lookup' "$workdir/valid_output"
grep -q 'method loop_entry_environment' "$workdir/valid_output"
grep -q 'function increment' "$workdir/valid_output"
grep -q 'method method_form' "$workdir/valid_output"
grep -q 'function ordered' "$workdir/valid_output"
grep -q 'if ' "$workdir/valid_output"
grep -q 'set<int>' "$workdir/valid_output"
grep -q 'map<int, int>' "$workdir/valid_output"
grep -q 'setFromSeq' "$workdir/valid_output"
grep -q ':|' "$workdir/valid_output"
grep -q '.Keys' "$workdir/valid_output"
grep -q '.contains' "$workdir/valid_output"
grep -q 'new List<int>(\[\])' "$workdir/valid_output"
grep -q 'while true' "$workdir/valid_output"
grep -q 'continue;' "$workdir/valid_output"
grep -q 'verifier finished with [0-9][0-9]* verified, 0 error' "$workdir/valid_output"
# Dafny 4.11 reports harmless warnings (for example, an `old` expression that
# does not dereference the heap) on stderr. A zero exit code and a zero-error
# verifier summary are the validity checks; warnings are intentionally
# tolerated here.

run_rejected_program() {
  local filename="$1"
  local message="$2"
  set +e
  (
    cd "$workdir"
    "$main_exe" \
      --mypy "$mypy_bin" \
      --dafny "$dafny_bin" \
      --prelude "$prelude" \
      --list "$list_library" \
      --temp-root "$workdir" < "$filename" > rejected_output 2> rejected_errors
  )
  local status=$?
  set -e
  test "$status" -eq 1
  grep -q "$message" "$workdir/rejected_errors"
}

# Unsupported effectful comparison operands must be rejected before they can
# become method calls nested in Dafny expression syntax.
cat > "$workdir/effectful_chain.py" <<'PYTHON'
def invalid_chain(xs: list[int]) -> bool:
  return xs.copy()[0] < 2
PYTHON
run_rejected_program effectful_chain.py 'effectful calls are unsupported in comparison chains'

# Effectful calls cannot appear in the lazy right-hand side of a short-circuit
# expression, where Dafny only accepts expression-level calls.
cat > "$workdir/scoped_effect.py" <<'PY'
def invalid_scoped(xs: list[int]) -> list[int]:
  return True and xs.copy()
PY
run_rejected_program scoped_effect.py 'effectful calls are unsupported in scoped expressions'

# The indexed lowering captures the initial list length, so mutating the
# iterated list would silently diverge from Python's iterator semantics.
cat > "$workdir/list_iteration_mutation.py" <<'PY'
def invalid_list_iteration(xs: list[int]) -> None:
  for item in xs:
    xs.append(item)
PY
run_rejected_program list_iteration_mutation.py 'mutating list while iterating it is unsupported'

cat > "$workdir/list_alias_mutation.py" <<'PY'
def invalid_list_alias(xs: list[int]) -> None:
  ys = xs
  for item in xs:
    ys.append(item)
PY
run_rejected_program list_alias_mutation.py 'mutating list while iterating it is unsupported'

cat > "$workdir/map_iteration_mutation.py" <<'PY'
def invalid_map_iteration(mapping: dict[int, int]) -> None:
  for key in mapping:
    mapping[2] = key
PY
run_rejected_program map_iteration_mutation.py 'map updates while iterating are unsupported'

cat > "$workdir/map_iteration_order.py" <<'PY'
def invalid_map_order(mapping: dict[int, int]) -> None:
  for key in mapping:
    break
PY
run_rejected_program map_iteration_order.py 'order-dependent behavior in map iteration is unsupported'

# List objects are functional in the runtime and do not have an index setter.
cat > "$workdir/list_assignment.py" <<'PYTHON'
def invalid_assignment(xs: list[int]) -> None:
  xs[0] = 2
PYTHON
run_rejected_program list_assignment.py 'indexed assignment into List is unsupported'

# Function pre/post and frame clauses are not valid specifications on a while
# statement; users must express loop facts as invariants or decreases clauses.
cat > "$workdir/loop_spec.py" <<'PYTHON'
def invalid_loop() -> None:
  # pre True
  while False:
    pass
PYTHON
run_rejected_program loop_spec.py 'loop specifications support only invariant and decreases'
