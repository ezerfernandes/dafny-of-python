# Phase 3 Set and Dictionary Support

## Status

Approved design for the next implementation slice after Phase 2. The phase
keeps the project’s value-style collection subset: Dafny sets and maps are
immutable values, and Python mutation or ordering behavior that cannot be
represented soundly is rejected.

## Scope

Phase 3 supports typed construction, lookup, membership, length, equality,
set algebra, iteration, and local functional dictionary updates. It covers
empty and populated displays, `set()` and `dict()`, duplicate dictionary keys,
collection values nested in expressions, and use in functions, methods,
loops, assertions, and specifications.

The phase explicitly excludes mutable wrapper runtimes, alias-observable
mutation, insertion-order semantics, unsupported collection methods, and
comprehensions. Comprehensions remain Phase 4.

## Architecture

The existing pipeline remains the authority for translation:

    parse -> normalize -> semantic analysis -> typed lowering -> Dafny emission

The semantic environment resolves collection kinds and their element or
key/value types. Existing source and Dafny collection nodes are retained
where their semantics match the target:

- `Set` and `Dict` represent source displays.
- `DSetExpr` and `DMapExpr` represent Dafny values.
- `DNativeIndex` represents native sequence, array, and map indexing.
- `DLen` represents cardinality for value collections.

The Dafny AST gains explicit nodes for map functional updates and set/map
iteration bindings. This prevents updates and choose-style iteration from
being confused with ordinary indexing or local assignment.

## Source and semantic rules

- `set()` lowers to an empty typed Dafny set when its type is known.
- `dict()` lowers to an empty typed Dafny map when its key and value types are
  known.
- Set displays lower to Dafny set displays after recursively lowering their
  elements.
- Dictionary displays evaluate entries from left to right and apply entries
  as sequential functional updates, so the rightmost equal key wins.
- `in` and `not in` lower to Dafny membership operations with operands checked
  against the collection type.
- Equality is accepted for compatible sets and maps and emitted as ordinary
  Dafny equality.
- `len` lowers to cardinality for sets/maps and retains the list runtime
  method for lists.
- Set union, intersection, and difference use explicit source operators and
  map to Dafny’s corresponding value operators.
- A local assignment such as `mapping[key] = value` becomes a functional map
  update of `mapping`. Updates through fields, nested indexes, or aliases are
  rejected because their Python aliasing semantics are outside this subset.

## Iteration

The semantic environment classifies the iterable before loop lowering:

- Lists and sequences retain indexed loop lowering.
- Sets iterate over a remaining set, choosing one member per iteration and
  removing it from the remaining value.
- Maps are rejected during iteration because Dafny map keys are exposed as an
  unordered set, while Python dictionaries preserve insertion order.

Set iteration requires a single supported loop target. Unsupported
destructuring and assumptions about iteration order produce translator
errors. The remaining set is paired with a decreasing cardinality so the
generated loop has a Dafny termination argument.

## Evaluation order and effects

Every lowered expression continues to carry its prelude, result, resolved
type, control-flow flag, and effect flag. Collection elements, dictionary
keys and values, and update operands are lowered left to right. No effectful
call is hoisted across a conditional or collection scope.

## Diagnostics

Semantic analysis rejects before Dafny invocation:

- missing concrete collection element, key, or value types;
- invalid membership, equality, algebra, or indexing operands;
- map iteration, because the target representation cannot preserve Python
  dictionary insertion order;
- map lookup where the enclosing specification has no available membership
  guarantee;
- functional updates through fields, nested indexes, or aliases;
- mutating methods such as `add`, `remove`, `pop`, and `setdefault`;
- unsupported multi-target/destructuring collection loops; and
- order-dependent dictionary behavior.

Diagnostics use the relevant source segment whenever one is available.

## Verification

The implementation adds parser and AST-shape tests, semantic positive and
negative tests, lowering and emitter golden tests, source-map assertions,
state-isolation tests, and real pinned mypy/Dafny 4.11 fixtures. The required
checks are:

    make test
    make coverage
    make integration
    git diff --check

The exact 100% Python and OCaml coverage gates remain mandatory.
