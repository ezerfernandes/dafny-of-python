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
cat > "$workdir/mypy-succeeds" <<'SCRIPT'
#!/usr/bin/env bash
printf 'mypy ok\n'
SCRIPT

cat > "$workdir/dafny-reports" <<'SCRIPT'
#!/usr/bin/env bash
printf '%s\n' "$@" > "$DAFNY_OF_PYTHON_DAFNY_ARGS"
printf 'verification warning\n' >&2
printf 'verifier finished with 1 verified, 0 errors\n'
SCRIPT
chmod +x "$workdir/mypy-fails" "$workdir/mypy-succeeds" "$workdir/dafny-succeeds" "$workdir/dafny-reports"

# Defaults must not be resolved before --help is handled. Running from a
# directory without src/libs/run makes this regression test meaningful.
(cd "$workdir" && "$main_exe" --help > help.out 2> help.err)
grep -q -- '--prelude' "$workdir/help.out"
test ! -s "$workdir/help.err"

# Explicit runtime paths must work even when the executable is isolated from
# both the source tree and an installed runtime directory.
explicit_exe="$workdir/explicit-main.exe"
cp "$main_exe" "$explicit_exe"

export DAFNY_OF_PYTHON_DAFNY_ARGS="$workdir/dafny.args"
set +e
(cd "$workdir" && printf 'x = 1\n' | "$explicit_exe" \
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

# Successful typechecking, verifier diagnostics, and --temp-root exercise the
# other CLI result path while keeping the temporary artifacts private.
set +e
(cd "$workdir" && printf 'x = 1\n' | "$main_exe" \
  --mypy "$workdir/mypy-succeeds" \
  --dafny "$workdir/dafny-reports" \
  --prelude "$prelude" \
  --list "$list_library" \
  --temp-root "$workdir" ignored-argument > success.out 2> success.err)
status=$?
set -e
test "$status" -eq 0
grep -q 'verification warning' "$workdir/success.err"
test ! -e "$workdir/program.py"
test ! -e "$workdir/program.dfy"

# Runtime resources can be discovered through the environment when callers do
# not want to pass installation-specific paths explicitly.
runtime_dir="$workdir/runtime"
mkdir "$runtime_dir"
cp "$prelude" "$runtime_dir/prelude.dfy"
cp "$list_library" "$runtime_dir/list.dfy"
(cd "$workdir" && DAFNY_OF_PYTHON_RUNTIME_DIR="$runtime_dir" printf 'x = 1\n' | \
  DAFNY_OF_PYTHON_RUNTIME_DIR="$runtime_dir" "$main_exe" \
  --mypy "$workdir/mypy-succeeds" \
  --dafny "$workdir/dafny-succeeds" > env.out 2> env.err)
test ! -s "$workdir/env.err"

# A missing runtime installation is reported by the top-level exception
# handler instead of producing an OCaml backtrace.
isolated_exe="$workdir/isolated-main.exe"
cp "$main_exe" "$isolated_exe"
set +e
(cd "$workdir" && env -u DAFNY_OF_PYTHON_RUNTIME_DIR printf 'x = 1\n' | \
  env -u DAFNY_OF_PYTHON_RUNTIME_DIR "$isolated_exe" \
  --mypy "$workdir/mypy-succeeds" \
  --dafny "$workdir/dafny-succeeds" > missing.out 2> missing.err)
status=$?
set -e
test "$status" -eq 1
grep -q 'Unable to locate runtime resource prelude.dfy' "$workdir/missing.err"
