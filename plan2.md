# Python Feature Support Plan

> Status note: this file is a roadmap, not the complete language contract.
> The current contract is [`docs/supported-subset.md`](docs/supported-subset.md).
> `plan.md` is the separate toolchain and coverage plan and is intentionally
> left unchanged.

## Summary

The semantic/type-resolution layer and typed lowering foundation described by
the first phase are implemented. Singleton tuple normalization, comparison
chains, constrained set/dictionary lowering, and typed list/set/dictionary
comprehensions are implemented and exercised against real Dafny 4.11. The
remaining phases in this file are a forward-looking plan for classes and
generators; they must not be read as currently supported language features.

The project enforces exact 100% coverage for maintained Python and OCaml code.
The current test and integration commands are documented in the README and the
supported-subset contract.

## Current Feature Status

| Feature | Current status | Remaining scope |
| --- | --- | --- |
| Semantic/type-directed lowering | Implemented for the current collection and callable subset | Classes and generators |
| Singleton tuples | Implemented; `(x,)` and `x,` normalize to `x`; `()` remains unsupported | No singleton tuple identity or indexing |
| Comparison chains | Implemented with ordered, short-circuit lowering and single evaluation | Scoped effectful operands remain rejected |
| Lists and sequences | Typed construction, indexing, slicing, membership, equality, iteration, and supported methods | Indexed list assignment and mutation during iteration |
| Sets | Typed construction, empty construction with context, membership, length, equality, algebra, iteration, and comprehensions | Mutation methods |
| Dictionaries | Typed construction, empty construction with context, lookup, membership, length, equality, functional local updates, order-insensitive key iteration, and comprehensions | Alias-observable mutation and insertion-order iteration |
| Higher-order functions | Typed callable parameters, pure lambdas, and pure/effect-classified calls | General Python callable object semantics |
| Comprehensions | Typed list, set, and dictionary comprehensions with nested clauses and filters | Generator comprehensions and broader target forms |
| Classes | Not implemented | Fields, constructors, methods, self, allocation, and member assignment |
| Generator functions | Not implemented | `yield`, iterator declarations, calls, iteration, and yield specifications |

The current implementation is probed with real Dafny 4.11 through the
integration fixtures. Those fixtures cover typed and empty set/dictionary
construction, collection membership and equality, singleton tuples,
comparison chains, evaluation order, loop lowering, comprehensions, and the
intentional rejections for unsupported mutation and scoped effects. Classes,
generator functions and generator comprehensions remain future work and fail
before translation can accept them.

## Semantic Scope

### Sets and dictionaries

Dafny set and map values are immutable, whereas Python set and dict objects are mutable. Python dictionaries also preserve insertion order.

For this roadmap, implement an explicit value-style subset:

- Support construction, lookup, membership, length, iteration, equality, set algebra, functional updates, and comprehensions.
- Lower local updates to new Dafny values where aliasing is not observable.
- Reject mutation through aliases, order-dependent dictionary behavior, and unsupported methods with clear translator errors.
- Consider mutable Set and Dict runtime wrapper classes as a later project if full Python mutation semantics are required.

This preserves the current mapping to Dafny built-in set and map values and bounds the initial effort.

List, set, and dictionary comprehensions are included in the current semantic
scope. Generator comprehensions remain tied to generator support.

### Classes

Start with a statically typed class subset:

- Require annotations for instance fields.
- Support __init__, ordinary instance methods, self, field access and assignment, and object construction.
- Do not initially support inheritance, decorators, metaclasses, properties, nested classes, static methods, class methods, or dynamic attribute creation.

Python class inheritance does not map directly to Dafny. Dafny classes can extend traits, but one Dafny class does not inherit from another class. Inheritance should therefore be a separate design milestone.

### Generators

Use native Dafny iterators to preserve lazy execution and retained local state.

Initial support includes:

- Synchronous generator functions.
- yield expression as a statement.
- Iterator[T], Iterable[T], and Generator[T, None, None] return annotations.
- Generator construction and iteration.
- yield specifications.

Initial support excludes:

- yield from
- send, throw, and close
- generator return values
- async generators
- exception/finally interactions
- generator methods inside classes

## Phase 1: Semantic Analysis and Unified Lowering (implemented baseline)

This phase is a prerequisite for the requested features.

### Symbol and type environment

Add a semantic-analysis pass that records:

- Variable and parameter types.
- Function signatures.
- Whether a callable is a pure function, method, constructor, or generator.
- Class definitions, fields, and methods.
- Collection element, key, and value types.
- Lexical scopes for functions, classes, and comprehensions.

The pass does not need to replace mypy as a complete Python type checker. It must retain enough type information to choose a correct Dafny representation and lowering rule.

### Generic type representation

Generalize the type AST instead of adding one hard-coded constructor for every generic:

    TGeneric(identifier, type_arguments)

This should support Iterator[int], Generator[int, None, None], user classes, and future generic containers.

Existing built-in type constructors may be retained temporarily and normalized into the generic representation during semantic analysis.

### Type-directed operations

Replace collection-blind transformations with type-directed lowering:

- List index becomes the List runtime's atIndex method.
- Sequence index becomes Dafny value[index].
- Dictionary index becomes Dafny map[key].
- Tuple index becomes a statically selected tuple field.
- List length becomes the List runtime's len method.
- Set, map, tuple, and sequence length becomes Dafny cardinality.
- Calls to a function, method, constructor, and generator receive distinct target representations.

### Lvalues

Replace the identifier-only Dafny assignment target with explicit lvalues:

    Local
    Field
    Index
    TupleTarget

This is required for class fields, collection updates, and destructuring.

### Unified expression lowering

The implementation uses a shared typed lowering API for the former
Convertcall/Convertlist responsibilities. It recursively handles supported
expression nodes, including expressions nested inside sets, dictionaries,
tuples, conditions, calls, and the typed comprehension lowering path.

Represent a lowered expression with:

- Prelude statements.
- Result expression.
- Resolved type.
- Conditional control flow where short-circuit evaluation is required.

This avoids the current eager call-hoisting problem and provides one place to enforce Python's left-to-right evaluation order.

### Baseline status

- Dictionary, tuple, sequence, and list indexing are distinguished correctly.
- Adding a source expression node causes exhaustive-match failures until every relevant pass handles it.
- Nested collection and call expressions are never silently skipped.
- Existing behavior, tests, and exact coverage remain green.

The baseline is complete for lists, sequences, tuples, sets, maps, callable
classification, alias tracking, source-aware diagnostics, and ordered
expression lowering. Class and generator symbols remain roadmap items rather
than supported declarations. Source-map reporting currently selects the
nearest original segment for generated diagnostics; exact locations for every
generated temporary remain a follow-up quality improvement.

## Phase 2: Singleton Tuples and Operator Chaining (implemented)

These are the smallest independently deliverable requested features.

### Singleton tuples

- Normalize Tuple [value] to value.
- Normalize TTuple [type] to type.
- Apply normalization recursively in parameters, return types, aliases, collection element types, callable signatures, and nested tuples.
- Cover x,, (x,), returns, assignments, and arguments.
- `()` remains unsupported and is rejected by the parser/normalization path.
- Document that singleton tuple identity and indexing are unavailable after normalization, as required by this translation rule.

The source AST should retain the comma's source segment until normalization so source maps can point at the original tuple syntax.

### Operator chaining

The source AST uses a dedicated node:

    CompareChain(first, [(operator, operand), ...])

The parser does not construct nested `BinaryExp` nodes for comparison chains.

Lower:

    a < b > c

to the equivalent of:

a < b && b > c

The lowering must ensure:

- Operands are evaluated left-to-right.
- Every middle operand is evaluated at most once.
- Later operands are skipped after a false comparison.
- Calls with effects are not eagerly hoisted.
- Mixed comparison directions are accepted.
- Membership comparisons participate where Python permits them.

The conceptual conjunction is lowered with scoped bindings where needed, so
the implementation does not rely on Dafny's native comparison-chain rules.
The implementation uses scoped bindings where necessary rather than eagerly
hoisting calls into an outer statement prelude. Effectful calls that cannot be
represented legally inside the scoped expression are rejected.

### Acceptance fixtures

- a < b < c
- a < b > c
- a == b != c
- x in xs == flag
- Chains containing function and method calls.
- A short-circuit case in which the final call must not execute.
- Chaining inside specifications, assertions, and conditionals. Chaining in
  comprehension filters are covered by the Phase 4 fixtures.

## Phase 3: Set and Dictionary Support (implemented constrained subset)

### Sets

The implemented subset includes:

- Populated displays such as {1, 2}.
- set() as an empty set.
- set(iterable) where the iterable type is known.
- Membership and non-membership.
- len.
- Equality.
- Union, difference, and intersection.
- Iteration.
- Nested typed calls, lists, and tuples inside displays.

Set comprehensions are covered in Phase 4.

Use Dafny set displays, {}, in, !in, cardinality, union, difference, and intersection.

### Dictionaries

The implemented subset includes:

- Empty and populated displays.
- Duplicate keys, with the rightmost value winning.
- Lookup as map[key].
- Key membership and non-membership.
- len.
- Equality.
- Iteration over keys.
- Functional update as map[key := value] where allowed by the subset.
- `keys()`, `values()`, and `items()` are not part of the current subset.

Dictionary comprehensions are covered in Phase 4.

Statically reject:

- Lookup without a key-membership proof where Dafny requires one.
- Unsupported mutation and aliasing.
- Order-sensitive behavior.
- Unsupported methods such as pop or setdefault.
- Mutable dictionary keys or set members that cannot map soundly to Dafny values.

### Generalized iteration

The existing for-loop lowering assumes a length and numeric subscript. Replace it with type-directed iteration:

- List: numeric index through the List runtime.
- Sequence and tuple: numeric index.
- Set: consume an unvisited set with a decreasing remainder.
- Dictionary: iterate over an unordered key set only when the loop body is
  order-insensitive; reject order-dependent behavior.
- Generator: use its iterator protocol in Phase 6.

### Acceptance criteria

- Every supported collection fixture passes mypy and verifies under Dafny 4.11.
- Invalid operations fail in semantic analysis before Dafny is invoked.
- Empty set and empty dictionary are unambiguous.
- Collection operations work in functions, methods, loops, and specifications.
  Comprehensions are covered by Phase 4.

## Phase 4: List, Set, and Dictionary Comprehensions (implemented)

The source AST uses typed comprehension nodes:

    ListComprehension(result, clauses)
    SetComprehension(result, clauses)
    DictComprehension(key, value, clauses)

Support:

- List comprehensions.
- Set comprehensions.
- Dictionary comprehensions.
- Multiple nested for clauses.
- Multiple filters.
- One identifier target per `for` clause.
- Proper nested lexical scope.
- Pure calls and conditional expressions in iterables, filters, keys, values,
  and results. Effectful calls in scoped filters remain rejected.

Lower list, set, and dictionary comprehensions into explicit accumulator code:

- List: construct a temporary runtime list and append each result.
- Set: initialize {} and accumulate with set union.
- Dictionary: initialize map[] and accumulate with map update.
- Nest loops and conditions in source order.

This gives consistent behavior across collection kinds and avoids relying on Dafny's proof restrictions for finite map comprehensions.

Comprehension targets must not leak into the enclosing scope. The iterable in the leftmost for clause must be evaluated in the enclosing scope; remaining clauses execute in the comprehension scope.

Generator expressions will use the same clause representation but are
completed in Phase 6.

### Remaining unsupported comprehension forms

- Async comprehensions.
- Assignment expressions.
- Starred targets or results beyond the existing target subset.
- yield inside the comprehension scope.

### Acceptance fixtures

- [x * x for x in xs]
- [x for x in xs if x > 0]
- [x + y for x in xs for y in ys if x < y]
- {x: x * x for x in xs}
- Nested `for` clauses and filters without variable leakage.
- Pure calls in clause and result positions.
- Empty output and duplicate set/dictionary keys.

## Phase 5: Classes

### Source representation

Extend the Python AST with a class declaration containing:

- Class name.
- Typed fields.
- Optional constructor.
- Instance methods.
- Source segments for the declaration and members.

Predeclare class names before analyzing members so methods can refer to their enclosing class and to classes declared later in the module.

### Dafny representation

Extend the Dafny AST and emitter with:

- Class declarations.
- Mutable fields.
- Constructors.
- Instance functions and methods.
- this.
- Object allocation.
- Field reads and writes.

### Translation rules

- Python class becomes a Dafny class.
- Typed field declarations become Dafny fields.
- __init__ becomes a Dafny constructor.
- Remove the explicit Python self parameter.
- self.x becomes this.x.
- self.x = value becomes a field assignment.
- C(args) becomes new C(args).
- A method that modifies fields receives an appropriate modifies this clause or requires an explicit source specification.
- A pure, expression-bodied method may become a Dafny function when its body and specifications allow it.
- User class annotations become Dafny reference types.

Class construction must participate in expression lowering because Dafny allocation is not an ordinary pure function call.

### Acceptance fixture

    class Counter:
        value: int

        def __init__(self, value: int) -> None:
            self.value = value

        # modifies self
        # post self.value == old(self.value) + 1
        def increment(self) -> None:
            self.value += 1

        def get(self) -> int:
            return self.value

The generated class must verify under Dafny 4.11, including:

- Constructor allocation.
- Field initialization.
- Field modification.
- Pure field-reading methods.
- Calls between instance methods.
- Source-mapped verification failures.
- Multiple instances with independent state.

### Explicit rejections

Emit precise diagnostics for:

- Inheritance.
- Decorators.
- Static and class methods.
- Properties and descriptors.
- Dynamic attributes.
- Class variables with Python shared-state semantics.
- Nested classes.
- Multiple __init__ definitions.
- Unannotated fields.

## Phase 6: Generator Functions and Generator Expressions

### Parser and Python AST

Add:

- A YIELD token.
- Yield expression as a statement.
- Iterator[T], Iterable[T], and supported Generator[Y, None, None] annotations.
- Generator-function classification based on yield in the body.
- Generator comprehension expressions.

When class support is present, a yield inside a nested method must not incorrectly classify the containing function or class.

### Dafny AST and emitter

Add:

- Iterator declarations.
- Yield parameters.
- Yield statements.
- Iterator construction.
- MoveNext consumption loops.
- Iterator-specific specifications.

### Generator lowering

Translate:

    def values(xs: list[int]) -> Iterator[int]:
        for x in xs:
            yield x

to a Dafny iterator that:

1. Declares a typed yield parameter.
2. Assigns the next value to the parameter.
3. Executes yield.
4. Retains its locals and control position.

Calling a generator allocates its iterator rather than invoking an ordinary function.

Iteration over a generator lowers to:

1. Construct the iterator.
2. Maintain Valid() and freshness invariants.
3. Call MoveNext().
4. Stop when MoveNext returns false.
5. Bind the current yield value.
6. Execute the Python loop body.

### Generator specifications

Extend specification comments with yield-specific forms, for example:

    # yield post value >= 0

Map:

- Ordinary preconditions to iterator-construction requirements.
- Ordinary postconditions to completion guarantees.
- Yield postconditions to yield ensures.
- Reads, modifies, and decreases to the corresponding iterator clauses.

Document generated history fields and make them available to advanced specifications where useful.

### Generator expressions

Reuse the comprehension clause representation. Synthesize a private iterator declaration for each generator expression, capturing required enclosing values explicitly.

Preserve Python's evaluation rule:

- Evaluate the leftmost iterable when the generator expression is created.
- Evaluate later iterables, filters, and results lazily during iteration.

### Acceptance criteria

- Multiple yields preserve local state.
- Yield inside if, while, and for works.
- Calling a generator does not execute its body eagerly.
- Consumer loops receive each yielded value exactly once.
- Generator expressions reuse comprehension lowering.
- Nested generators have isolated state.
- Unsupported yield from, send, async, and generator return values fail with explicit diagnostics.

## Cross-Cutting Testing Requirements

Every feature slice must add:

- Lexer tests.
- Parser and AST-shape tests.
- AST serialization tests.
- Semantic-analysis and scope tests.
- Lowering tests.
- Dafny emitter golden tests.
- Real mypy and Dafny 4.11 verification.
- Negative tests for unsupported forms.
- Source-map assertions.
- Repeated-run state-isolation tests.
- Exact 100% OCaml and Python coverage.

No feature is complete merely because it parses. Generated Dafny must pass the real-tool integration suite.

### End-to-end fixtures

Maintain a small executable specification corpus covering:

- A class with construction, mutation, and a pure observer.
- A generator with multiple yields and a consuming loop.
- List, set, dictionary, and generator comprehensions.
- Mixed-direction chained comparisons with calls.
- Populated and empty sets and dictionaries.
- Dictionary lookup under a membership precondition.
- Singleton tuple values and types.
- Interactions, such as a class method returning a comprehension over a generator.

### Coverage gate

Continue requiring:

    make test
    make coverage
    make real-integration

The permanent gate remains exactly 100%, not a rounded threshold. New source files must be included in the Bisect expectation scan, and any generated-code exclusions must be documented.

## Delivery Sequence

Use separate reviewable pull requests or commits. The first six slices are
implemented in the current branch; the remaining slices are future work:

1. Semantic environment, generic types, explicit lvalues, and type-directed subscripts. *(implemented baseline)*
2. Unified expression and evaluation-order lowering. *(implemented baseline)*
3. Singleton tuple normalization. *(implemented)*
4. Comparison chains. *(implemented)*
5. Constrained set and dictionary operations. *(implemented; order-sensitive map iteration and alias-observable mutation remain rejected)*
6. List, set, and dictionary comprehensions. *(implemented; generator comprehensions remain future work)*
7. Class declarations, fields, and constructors.
8. Class methods and object construction.
9. Generator declarations and yield.
10. Generator consumption and expressions.
11. Cross-feature fixtures, documentation, and final cleanup.

Each change should preserve the existing 100% coverage gate rather than deferring tests until the end.

## Definition of Done

For every supported feature:

- The accepted syntax is documented.
- The parser preserves the necessary source locations.
- Semantic analysis resolves all relevant names and types.
- The generated Dafny 4.11 source is syntactically valid.
- The real verifier accepts positive fixtures.
- Negative fixtures fail in the translator with a relevant source-mapped error;
  exact generated-temporary columns may remain approximate.
- Python evaluation order and the documented subset semantics are preserved.
- Repeated translations are deterministic.
- The full test, coverage, and real-tool integration gates pass.

## Estimate

Estimated effort for the restricted semantics described above:

| Work | Estimate |
| --- | ---: |
| Semantic and lowering foundation | 4-6 days |
| Singleton tuples and chains | 2-3 days |
| Sets and dictionaries | 4-6 days |
| Comprehensions | 4-7 days |
| Classes | 6-9 days |
| Generators | 6-10 days |
| Integration, source maps, and documentation | 2-4 days |
| **Total** | **28-45 engineering days** |

This is approximately six to nine weeks for one engineer.

Mutable set/dictionary aliasing, Python-compatible dictionary order, inheritance, generator methods, yield from, and advanced Python class behavior should be treated as follow-up projects.

## Reference Documentation

- [Python comparison semantics](https://docs.python.org/3/reference/expressions.html#comparisons)
- [Python comprehensions and generator expressions](https://docs.python.org/3/reference/expressions.html)
- [Python class definitions](https://docs.python.org/3/reference/compound_stmts.html#class-definitions)
- [Python generator functions](https://docs.python.org/3.12/reference/datamodel.html)
- [Python set and dictionary semantics](https://docs.python.org/3.12/reference/datamodel.html)
- [Dafny 4.11 documentation](https://dafny.org/v4.11.0/)
- [Dafny reference manual](https://dafny.org/dafny/DafnyRef/DafnyRef)
- [Dafny object-oriented programming](https://dafny.org/teaching-material/Lectures/1-3-Programming-ObjectOriented.html)
- [Dafny value and reference types](https://dafny.org/latest/HowToFAQ/FAQReferences)
