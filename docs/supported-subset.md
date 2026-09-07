# Supported typed-Python subset

This document is the contract for the translator as it exists today. It is
more precise than the long-term feature roadmap in [`plan2.md`](../plan2.md),
which also describes work that is not implemented yet.

The translator accepts a deliberately small, statically typed Python dialect.
Successful translation and Dafny verification establish the requested
properties for that dialect; they do not establish the behavior of arbitrary
Python programs.

## Toolchain

The supported integration toolchain is:

- Python 3.12;
- mypy 1.18.2, installed from `uv.lock`;
- OCaml 4.14.2 and the locked Opam dependencies; and
- Dafny 4.11.0 with the checked-in runtime libraries.

The CLI runs mypy and Dafny for every input. A successful mypy check is not a
substitute for Dafny verification, and a mypy failure is reported while the
translation continues. The CLI status is 0 when both tools succeed, 1 when
translation or Dafny fails, and 2 when only mypy fails.

## Module and declaration shape

Supported programs may contain:

- top-level assignments and assertions;
- top-level function declarations with typed parameters and return types;
- function bodies made from the statements listed below; and
- simple type aliases and single, unconstrained `TypeVar("T")` declarations.

`import` and `from ... import ...` lines are lexed and ignored. They do not
load modules or provide general Python import semantics. The README examples
use imports from `typing` only as source-level documentation.

Classes, nested function declarations, decorators, dynamic attributes, and
inheritance are not supported.

## Types

The supported annotations are:

- `int`, `float`, `bool`, `str`, `None`, and `object`;
- `list[T]` using the checked-in mutable runtime `List<T>`;
- `set[T]` using Dafny value sets;
- `dict[K, V]` using Dafny value maps;
- fixed-size `tuple[T1, ...]` values;
- `Callable[[T1, ...], R]`; and
- `Type[T]` where the current lowering can represent the resulting type.

Generic aliases are normalized before lowering. A `TypeVar` must have one
string argument matching its declaration; constrained or variadic type
variables are rejected.

Every collection used by a lowering rule must have concrete element, key, and
value types where Dafny requires them. Untyped empty collections are rejected
unless an annotation or expression context supplies the type.

## Expressions

The supported expression forms include:

- primitive literals, identifiers, unary and arithmetic/Boolean operators;
- function calls, callable parameters, pure lambdas, and conditional
  expressions;
- `len`, `max`, `old`, and `fresh` in the contexts where their Dafny meaning
  is available;
- `forall` and `exists` quantifiers;
- list, set, dictionary, array, and fixed-size tuple displays;
- list, set, and dictionary comprehensions with one-identifier targets,
  nested `for` clauses, and `if` filters;
- singleton tuples written as `(x,)` or `x,`, which normalize to `x`;
- multi-element tuples with statically known integer indexes;
- chained comparisons, with Python's left-to-right, short-circuit, and
  single-evaluation behavior;
- list indexing and slicing;
- sequence, array, and map native indexing; and
- set/map membership, equality, and set union, intersection, and difference.

Expression lowering preserves left-to-right evaluation when an earlier value
must be captured before a later value's prelude. Effectful calls remain
statement-level operations. An effectful call in a short-circuit, conditional,
quantifier, lambda, specification, or comparison-chain expression is rejected
when Dafny cannot represent it as a legal scoped expression.

## Collections and mutation policy

Lists use the runtime `List<T>` class. Construction, length, indexing, slicing,
membership, content equality, iteration, comprehensions, and the supported
runtime methods are available. List methods that mutate the receiver require
ordinary statement context and contribute to method frame inference. Indexed
list assignment is rejected because the runtime list has no index setter.

List iteration captures the source value and rejects mutations of the iterated
list, including mutations through tracked aliases. This avoids silently
changing Python's iterator behavior when the generated loop uses indexed
lowering.

Sets and dictionaries use Dafny's immutable value representations. Supported
operations include typed construction, empty construction with a known type,
membership, length, equality, set algebra, comprehensions, dictionary lookup
with a proven key, and local functional dictionary updates.

The value-style policy rejects updates through aliases, function map
parameters, returned map aliases, unsupported mutating collection methods,
unhashable set elements or dictionary keys, and map lookups without a
membership/key-presence proof. These rejections are intentional: silently
translating Python object mutation to value replacement would verify the wrong
program.

Dictionary key iteration is supported only for order-insensitive loop bodies.
The generated loop uses an unordered key set, so order-dependent behavior,
including `break`, `return`, assignment, or effectful operations whose result
depends on key order, is rejected. Python insertion-order semantics are not
promised by this subset.

## Statements and specifications

Supported statements include:

- local assignment, annotated assignment, tuple-target assignment, and
  supported map functional updates;
- `if`/`elif`/`else`;
- `while` with `invariant` and `decreases` specifications;
- typed `for` loops over supported lists, sequences, sets, and order-insensitive
  dictionary key iteration;
- `return`, `assert`, `pass`, `break`, and `continue`; and
- supported augmented arithmetic assignments.

Function specifications support `pre`, `post`, `reads`, and `modifies`.
Loop specifications support only `invariant` and `decreases`; function
specifications copied onto a `while` statement are rejected.

Loop targets are limited to the target forms implemented by the typed lowering
path. Unsupported destructuring, nested collection mutation, and unsupported
assignment targets are rejected before Dafny is invoked.

## Explicitly unsupported roadmap features

The following are future work, not accidentally omitted guarantees:

- generator functions, `yield`, and generator expressions;
- classes and object construction;
- inheritance, decorators, properties, async constructs, and exceptions;
- full Python mutable set/dictionary alias semantics;
- insertion-order-preserving dictionary iteration; and
- arbitrary imports and the Python standard library.

`()` remains unsupported. A comma-bearing singleton tuple is intentionally
normalized to its element and does not retain tuple identity or support
singleton indexing.

Comprehensions are lowered to explicit accumulator loops. They are evaluated
eagerly, preserve clause order, keep their targets in a comprehension-local
scope, and reject comprehensions in Dafny scoped-expression contexts. Tuple,
starred, assignment-expression, async, and `yield` targets/results are not
part of this subset.

## Diagnostics and source locations

Semantic and lowering errors are reported before Dafny when the subset rule is
known locally. Dafny diagnostics are mapped back through the generated
source map to the nearest original Python segment. Generated temporaries and
runtime-library positions can therefore produce an approximate or dummy
location; the mapping is intended to identify the relevant source construct,
not to promise a stable column for every generated token.

The real-tool fixtures and the unit tests are the executable compatibility
contract for accepted and rejected cases. Run them with:

```sh
make test
make real-integration
make coverage
```
