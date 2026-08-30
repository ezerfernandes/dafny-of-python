# uv Migration and 100% Test Coverage Plan

## Summary

This is primarily an OCaml project, not a Python package. The appropriate migration is therefore:

- Use **uv** to manage the Python runtime and `mypy` dependency.
- Continue using **Dune** to build and test the OCaml code.
- Add **Opam** metadata and locking for reproducible OCaml dependencies.
- Install and pin **Dafny 4** separately; uv cannot manage it.

The repository currently has effectively no automated tests, no reproducible OCaml dependency manifest, no Python dependency manifest, and no CI. Reaching 100% coverage will require testability refactoring, dead-code decisions, broad unit and integration coverage, and an enforced coverage gate.

## Current State

- There is no `pyproject.toml`, requirements file, or Python lockfile. This is a uv adoption rather than a migration from another Python package manager.
- The executable invokes `mypy` and `dafny` directly and writes fixed `program.py` and `program.dfy` files into the working directory.
- There are approximately 2,384 lines of compiled OCaml source and another 481 lines of dormant code under `src/libs/type` and `src/libs/solver`.
- The only test declaration is an empty inline-test module in `src/libs/parse/parser.ml`.
- There is no `.opam` dependency manifest or CI configuration.
- The root `dune-project` and nested `src/dune-project` should be consolidated.
- A baseline coverage number cannot currently be measured because the environment lacks OCaml, Dune, Opam, mypy, and Dafny.
- Generated output now targets Dafny 4 syntax. The translator must stay pinned to a
  tested Dafny 4 release because verifier diagnostics and library behavior can
  change between releases.
- Several transformation and emitter modules contain mutable global state, making repeated tests potentially order-dependent.
- The code contains unsupported, exceptional, duplicate, and possibly unreachable paths that must be tested, removed, or redesigned before an honest 100% result is possible.

## Coverage Definition

The recommended target is:

> 100% Bisect_ppx expression-point coverage across every maintained, handwritten, compiled production OCaml module.

Additional rules:

- Generated Menhir/ocamllex implementation internals may be excluded, but lexer and grammar behavior must still be exercised through tests.
- Every maintained compiled source file must be checked with Bisect_ppx `--expect`, preventing a file from disappearing silently from the report.
- Test code itself is not included in the production coverage denominator.
- Unsupported and error behavior must be tested where it is part of the public contract.
- Coverage exclusions must be narrow, documented, and reviewed. They must not be used to hide difficult handwritten logic.

### Dormant-code decision

Before enforcing the gate, decide how to treat `src/libs/type` and `src/libs/solver`, which are tracked but not built:

1. **Recommended:** classify them as abandoned prototypes and remove or archive them.
2. Add them to Dune, repair incomplete code, and test them as maintained production modules.

They must not be silently omitted while claiming 100% coverage for all existing repository code.

## Implementation Plan

### Phase 1: Establish reproducible toolchains

1. Consolidate the repository around one root `dune-project`.
2. Declare all OCaml dependencies in generated or maintained `.opam` metadata, including:
   - `ocaml`
   - `dune`
   - `core`
   - `base`
   - `stdio`
   - `sexplib`
   - `ppx_jane`
   - `menhir`
   - `re2`
   - the selected test framework
   - `bisect_ppx` for development and coverage
3. Create a local Opam switch and lock the resolved dependency set.
4. Run a compatibility spike against all README examples.
5. Pin a compatible Dafny 4.x release, currently Dafny 4.11.0, and keep the
   generated syntax aligned with that release.
6. Record the exact OCaml, Dune, Python, mypy, and Dafny versions.

Acceptance criteria:

- A clean clone can install dependencies and build without undocumented global packages.
- The README examples translate under the pinned tool versions.
- The selected versions are recorded in committed manifests or documentation.

### Phase 2: Adopt uv for Python dependencies

Create and commit:

- `pyproject.toml`
- `uv.lock`
- `.python-version`
- `.venv` ignore rule

Configure the repository as a non-package uv project:

```toml
[tool.uv]
package = false
```

Place `mypy` in the locked runtime dependency set because it is required by the OCaml CLI, not merely by tests. Select and pin its compatible version after running the sample corpus.

Canonical commands should use the frozen lockfile:

```sh
uv sync --frozen
uv run --frozen -- opam exec -- dune runtest
```

Do not hard-code `uv run` inside the OCaml executable. Keep the executable's command runner configurable and invoke the project under `uv run`, which puts the locked `mypy` executable on `PATH` without coupling the installed binary to a source-tree lockfile.

Acceptance criteria:

- No manual virtualenv or pip installation is needed.
- `mypy` always comes from `uv.lock`.
- `uv sync --frozen` succeeds from a clean checkout.

### Phase 3: Refactor for deterministic testing

1. Extract translation and verification orchestration from the top-level `let ()` executable into a library.
2. Make the external command runner injectable.
3. Invoke programs with argument arrays rather than concatenated shell command strings.
4. Return subprocess exit status, stdout, and stderr explicitly.
5. Use temporary files and directories rather than fixed `program.py` and `program.dfy` files.
6. Pass prelude and runtime-library resource paths explicitly instead of assuming execution from the repository root.
7. Replace mutable global state with per-run context values, or provide explicit and reliable reset functions, in:
   - `Convertcall`
   - `Convertlist`
   - `Convertfor`
   - `Generics`
   - `Todafnyast`
   - `Emitdfy`
8. Pass sourcemaps into reporting functions rather than reading the emitter's global state.
9. Define the intended behavior when mypy or Dafny fails. The current mypy path prints an error and continues translating.
10. Add characterization tests before changing externally visible behavior.

Acceptance criteria:

- Unit tests can run without real external commands.
- Tests can run repeatedly and in any order.
- Test runs leave no `program.py`, `program.dfy`, or other persistent artifacts.
- The CLI is thin enough to exercise through integration tests.

### Phase 4: Build the test suite bottom-up

Use external Dune test executables with Alcotest or a comparable OCaml framework. Use golden or expectation tests where emitted text is the main result.

#### 4.1 Parser and source handling

Cover:

- Source-position and segment utilities.
- Lexer tokens and source locations.
- Indentation, dedentation, blank lines, comments, imports, and EOF behavior.
- Specification comments: preconditions, postconditions, invariants, decreases, reads, and modifies.
- Literals, identifiers, operators, collection syntax, type syntax, and illegal characters.
- Every maintained grammar construct.
- Parsing through string, channel, and file entry points.
- Lexing and parsing error paths.
- AST subtyping, type equality, and invalid identifier-list paths.
- The legacy `Exp` module's formatting functions if the module remains compiled; otherwise remove it as dead code.

#### 4.2 Transformation passes

Cover:

- `Convertcall`, including nested calls, calls in statements, and specification/invariant rewriting.
- `Convertlist`, including list construction, nested collections, indexing, and every slice-bound combination.
- `Convertfor`, including nested control flow and loop specifications.
- Generic and `TypeVar` conversion, including malformed and constrained definitions.
- All maintained type, operator, literal, expression, specification, statement, and top-level paths in `Todafnyast`.
- Explicit rejection paths for unsupported constructs.
- Unequal assignment lengths and other structural errors.

Tests should expose and resolve suspicious existing behavior, including the `Fresh` conversion path in `Convertcall` and duplicated/unreachable match branches.

#### 4.3 Emitter and reporting

Cover:

- Golden Dafny text for every maintained AST form.
- Indentation, declarations, assignments, return values, functions, methods, loops, and conditionals.
- All type and operator spellings.
- Sourcemap construction and nearest-location lookup.
- Repeated emissions to prove state isolation.
- Dafny success output, verification errors, malformed output, and output without errors.
- The fragile hard-coded `prelude_verified = 42` behavior: either characterize it under the pinned Dafny or replace it with a version-independent approach.

#### 4.4 Pipeline and CLI

Cover:

- Parse -> transform -> emit golden tests for all README examples.
- Representative examples for each supported language feature.
- Fake mypy/Dafny runners for success, rejection, missing executables, malformed output, and nonzero exits.
- stdin/stdout/stderr behavior and CLI exit codes.
- A small real integration matrix using uv-managed mypy and pinned Dafny.

Acceptance criteria:

- Tests cover successful and failing behavior at each layer.
- README examples are executable regression fixtures.
- Most coverage is supplied by focused unit tests; external-tool tests remain small and deterministic.

### Phase 5: Add and enforce Bisect_ppx coverage

1. Add Bisect_ppx instrumentation to every maintained production library and executable.
2. Add an explicit generated-code exclusion file where preprocessing cannot be avoided.
3. Remove old `.coverage` files before each coverage run.
4. Force every test to rerun under instrumentation:

   ```sh
   dune runtest --instrument-with bisect_ppx --force
   ```

5. Generate terminal, per-file, and HTML reports.
6. Run the report with `--expect` for all maintained source directories and explicit `--do-not-expect` entries only for reviewed exclusions.
7. Add a coverage-gate script that compares covered and total instrumentation points exactly; `bisect-ppx-report summary` reports coverage but does not itself provide a fail-under threshold.
8. Remove genuinely unreachable or duplicate handwritten code instead of excluding it.
9. Add exception assertions for meaningful failure branches.

Acceptance criteria:

- Every maintained handwritten compiled file is present in the coverage report.
- Covered instrumentation points equal total instrumentation points.
- The gate fails for 99.99% as well as lower values.
- An HTML report is available for diagnosing future regressions.
- The ordinary non-instrumented test command remains fast and simple.

### Phase 6: Add CI and documentation

Add CI that:

1. Installs uv and runs `uv sync --frozen`.
2. Creates the pinned Opam environment and installs build/test dependencies.
3. Installs the pinned Dafny release.
4. Builds the project with warnings checked.
5. Runs ordinary unit and integration tests.
6. Runs the instrumented suite and enforces exactly 100% coverage.
7. Publishes the HTML coverage report as an artifact.
8. Confirms that tests leave the working tree clean.

Update the README to:

- Remove the current `sudo dune exec` instruction.
- Explain the separate responsibilities of uv, Opam/Dune, and Dafny.
- List the supported and pinned tool versions.
- Document clean-clone setup.
- Provide canonical `build`, `test`, `coverage`, and `run` commands.
- Explain the precise coverage scope and reviewed exclusions.

Acceptance criteria:

- A pull request cannot merge when build, tests, lockfile checks, or the 100% coverage gate fail.
- A new contributor can reproduce CI locally from documented commands.

## Suggested Delivery Sequence

Keep the work reviewable through several small pull requests or commits:

1. Toolchain manifests, Dune consolidation, uv lockfile, and clean-clone build.
2. Coverage instrumentation and an initial baseline report.
3. Testability refactoring with characterization tests.
4. Parser and source utility tests.
5. Transformation tests.
6. Emitter and report tests.
7. Pipeline, CLI, and external-tool integration tests.
8. Dead/unreachable-code cleanup and final 100% gate.
9. CI and documentation.

Do not require 100% in the first instrumentation commit. Record the baseline, raise coverage monotonically during the test commits, and activate the permanent 100% gate only after the maintained-code scope is settled.

## Estimate

Expected effort: **8-14 engineering days**.

- Reproducible toolchains and uv adoption: 1-2 days
- Testability refactoring: 2-3 days
- Unit, golden, and integration suite: 4-7 days
- Final coverage gaps, CI, and documentation: 1-2 days

Add approximately 3-5 days if dormant code must be revived and covered, or if generated Dafny output must also migrate to Dafny 4.

## Risks

- The 2021 codebase may not compile unchanged against current Jane Street OCaml libraries.
- Current Dafny releases use different syntax and may emit different diagnostics from those expected by the report parser.
- Current mypy behavior may differ from the historical version used by the project.
- Mutable global state may reveal order-dependent output or sourcemap bugs.
- Exercising every error path is likely to reveal existing defects; reserve time for fixes rather than weakening tests.
- Bisect_ppx expression coverage is not proof of semantic correctness or exhaustive Boolean branch coverage. Golden tests, negative cases, and integration tests remain necessary even at 100%.

## Reference Documentation

- [uv non-package project setting](https://docs.astral.sh/uv/reference/settings/)
- [uv dependency management](https://docs.astral.sh/uv/concepts/projects/dependencies/)
- [uv command execution](https://docs.astral.sh/uv/concepts/projects/run/)
- [OCaml dependency management with Opam](https://ocaml.org/docs/managing-dependencies)
- [Dune testing](https://dune.readthedocs.io/en/stable/tests.html)
- [Bisect_ppx Dune usage](https://github.com/aantron/bisect_ppx#dune)
- [Bisect_ppx generated-code exclusions and `--expect`](https://github.com/aantron/bisect_ppx/blob/master/doc/advanced.md)
- [Dafny function syntax changes](https://dafny.org/latest/HowToFAQ/FAQFunctionMethodDiffs)
