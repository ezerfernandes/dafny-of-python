# Reproducible toolchain

The project has three independent toolchains:

| Tool | Responsibility | Pin/source |
| --- | --- | --- |
| uv | Python runtime and `mypy` executable | Python 3.12, `mypy==1.18.2`, `uv.lock` |
| Opam/Dune | OCaml compiler, libraries, build, and tests | OCaml 4.14.2 target, dependencies in `dafny-of-python.opam` |
| .NET tool | Dafny verifier and runtime libraries | Dafny 4.11.0 target |

The project is a non-package uv project. `uv sync --frozen` creates the virtual
environment and installs `mypy`, pytest, and pytest-cov; it does not install or
invoke the OCaml toolchain. `uv run --frozen -- opam exec -- ...` is the
canonical composition for commands that need both toolchains.

The local Opam switch is created with:

```sh
opam switch create . 4.14.2
opam install . --deps-only --locked
opam install alcotest bisect_ppx.2.8.3
```

The separate test-tool install is intentional: `bisect_ppx.2.8.3` publishes an
obsolete `ocamlformat=0.16.0` package-test dependency that is incompatible with
the OCaml 4.14.2 target when Opam is invoked with `--with-test`. The project
dependencies are still resolved by Opam from the manifest, while the required
test and coverage tools are installed without enabling that upstream package's
own tests.

The lock resolution is owned by Opam and should be regenerated with `opam
lock` whenever the dependency manifest changes. The checked-in manifest is the
source of truth for the direct dependency set, and
`dafny-of-python.opam.locked` records the currently supported OCaml 4.14.2
resolution. Regenerate it with:

```sh
opam lock ./dafny-of-python.opam
```

`make setup` runs the locked uv synchronization and the equivalent Opam setup.
CI performs the same resolution from a clean checkout. The lockfile preserves
the test filters; the explicit test-tool install remains necessary because
enabling all upstream package tests would reintroduce the incompatible
`ocamlformat=0.16.0` dependency.

Install Dafny 4.11.0 with:

```sh
dotnet tool install --global dafny --version 4.11.0
```

Dafny 4 is required because generated functions use Dafny 4's `function`
syntax. The CLI invokes the verifier as `dafny verify --allow-warnings`.
