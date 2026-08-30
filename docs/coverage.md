# Coverage policy

The maintained production scope is the handwritten OCaml under `src/bin`,
`src/libs/parse`, `src/libs/transform`, and `src/libs/run`. The CLI entrypoint
is exercised by `test/cli_test.sh`, including `--help`, explicit runtime paths,
and mypy-failure exit behavior. Generated Menhir and ocamllex implementation
files are not part of the source-tree expectation scan. They are excluded at
their source headers with `[@@@coverage exclude_file]`; their behavior is still
exercised through the public parser entry points. The handwritten
type-only `src/libs/transform/astdfy.ml` module has no executable Bisect_ppx
points and is explicitly excluded for the same reason.
The data-only AST and source-map declarations in `astpy.ml` and `sourcemap.ml`
similarly suppress only their ppx-generated sexp serializer points; handwritten
translation and source-map functions remain in the metric.

`src/libs/type` and `src/libs/solver` are archived prototypes: they are tracked
for historical reference, are not included by Dune, and are explicitly
excluded from the maintained-code coverage expectation. They must either be
removed or brought back into the build and covered before being treated as
production code.

Run the ordinary suites with:

```sh
make python-test
make ocaml-test
```

Run both coverage gates with:

```sh
make coverage
```

The gate removes stale `.coverage` files, forces every test to rerun under
Bisect_ppx, checks that every maintained `.ml` file is present, emits an HTML
report in `_coverage/html`, and requires OCaml expression-point coverage above
95%. Python coverage is measured with pytest-cov, including branch coverage,
and is also required to be above 95%. The verifier summary is
reported as Dafny emits it: its verified count includes `program.dfy`, the
prelude, and the list runtime library. Error locations are remapped only when
they correspond to generated-program source-map entries; runtime-library
locations may therefore resolve to the default source segment.
