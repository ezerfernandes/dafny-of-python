#!/usr/bin/env bash
set -euo pipefail

main_exe="$(realpath "$1")"
prelude="$(realpath "$2")"
list_library="$(realpath "$3")"
workdir="$(mktemp -d "${TMPDIR:-/tmp}/dafny-of-python-cli-test.XXXXXX")"
trap 'rm -rf "$workdir"' EXIT

cat > "$workdir/mypy-fails" <<'SCRIPT'
#!/usr/bin/env bash
echo "synthetic mypy error" >&2
exit 7
SCRIPT

cat > "$workdir/dafny-succeeds" <<'SCRIPT'
#!/usr/bin/env bash
printf '%s\n' "$@" > "$DAFNY_OF_PYTHON_DAFNY_ARGS"
printf 'verifier finished with 1 verified, 0 errors\n'
SCRIPT
chmod +x "$workdir/mypy-fails" "$workdir/dafny-succeeds"

# Defaults must not be resolved before --help is handled. Running from a
# directory without src/libs/run makes this regression test meaningful.
(cd "$workdir" && "$main_exe" --help > help.out 2> help.err)
grep -q -- '--prelude' "$workdir/help.out"
test ! -s "$workdir/help.err"

export DAFNY_OF_PYTHON_DAFNY_ARGS="$workdir/dafny.args"
set +e
(cd "$workdir" && printf 'x = 1\n' | "$main_exe" \
  --mypy "$workdir/mypy-fails" \
  --dafny "$workdir/dafny-succeeds" \
  --prelude "$prelude" \
  --list "$list_library" > output.out 2> output.err)
status=$?
set -e

# Typechecking is non-fatal to translation, but is visible to automation as
# exit code 2 when verification itself succeeds.
test "$status" -eq 2
grep -q 'Typechecking failed (exit code 7)' "$workdir/output.err"
grep -q '^verify$' "$workdir/dafny.args"
grep -q '^--allow-warnings$' "$workdir/dafny.args"
grep -q "$prelude" "$workdir/dafny.args"
grep -q "$list_library" "$workdir/dafny.args"
test ! -e "$workdir/program.py"
test ! -e "$workdir/program.dfy"
