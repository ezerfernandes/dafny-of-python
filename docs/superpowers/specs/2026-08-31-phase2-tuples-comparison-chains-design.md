# Phase 2: Singleton Tuples and Comparison Chains

## Scope

Phase 2 extends the semantic lowering pipeline with two Python expression
features described by `plan2.md`:

1. comma-bearing singleton tuples (`(x,)` and `x,`), which normalize to their
   single value; and
2. chained comparisons (`a < b > c`), which preserve Python's evaluation
   order, short-circuit behavior, and single evaluation of middle operands.

The empty tuple `()` remains unsupported. Multi-element tuples retain their
existing tuple identity and indexing behavior. This phase does not change the
legacy lowering path except where shared parser or AST definitions require
compatibility updates.

## Architecture

The source AST will distinguish comma-bearing singleton tuples from ordinary
parenthesized expressions. `SingletonTuple` stores the comma source segment
and its child expression. The lexer will attach source segments to comma
tokens, allowing the parser to preserve the source location until semantic
normalization. `(x)` continues to parse directly as `x`; the parser has no
empty-parentheses production, so `()` remains rejected.

The source AST will also gain `CompareChain`, containing the first operand and
an ordered list of `(operator, operand)` pairs. The comparison grammar will
construct this node directly rather than producing nested `BinaryExp` values.
A comparison with no comparison operator remains the underlying sum
expression. A comparison with one or more operators is represented as a
`CompareChain`.

Semantic normalization is a recursive pass that runs before type inference and
lowering. It removes `SingletonTuple` wrappers and one-element tuple values,
normalizes nested expressions and types, and visits every expression/type
position used by the program: declarations, parameters, returns, aliases,
collection element types, callable signatures, calls, assignments,
specifications, comprehensions, and binders. Empty tuples are not synthesized;
if one is supplied through a manually constructed AST, the semantic pipeline
reports it as unsupported.

## Comparison-chain lowering

The Dafny expression AST will gain a local-binding expression sufficient for
embedding scoped evaluation in an expression. A chain is lowered recursively
to nested bindings and conditional expressions. For example:

```text
a < b > c
```

becomes conceptually:

```text
let left = a;
let middle = b;
if left < middle then
  (let right = c; middle > right)
else
  false
```

Each operand is bound at the latest point at which Python would evaluate it.
The first operand and the first middle operand are evaluated before the first
comparison. Each later operand is evaluated only inside the successful branch
of the preceding comparison. A middle operand is referenced through its local
binding, so it is evaluated at most once. The operator list is emitted in
source order and supports mixed comparison directions and membership tests.

Calls with effects remain scoped in the generated expression and are never
hoisted into an outer prelude. If an operand needs statement-only setup that
cannot be represented by a scoped expression, lowering raises a precise
unsupported-expression error instead of changing evaluation order.

The chain result is boolean and is usable anywhere an expression is accepted,
including assertions, specifications, conditionals, and comprehension
filters. Existing boolean `and`/`or` lowering remains responsible for its own
short-circuit behavior; comparison-chain lowering explicitly builds its own
conditional structure.

## Error handling and compatibility

- `()` remains a parser error.
- Empty tuple nodes supplied outside the parser are rejected by the semantic
  phase with an unsupported-tuple diagnostic.
- Singleton normalization intentionally removes tuple identity and therefore
  does not expose singleton indexing.
- Multi-element tuples are unchanged.
- Existing AST constructors and legacy conversion behavior are retained where
  possible; new source and Dafny constructors are added as separate cases to
  minimize unrelated churn.
- Unsupported scoped operands fail deterministically with a diagnostic that
  identifies comparison-chain lowering as the source of the limitation.

## Testing and verification

Tests will cover:

- parsing `(x,)`, `x,`, `(x)`, multi-element tuples, and rejection of `()`;
- recursive singleton normalization in expressions and types;
- singleton tuples in returns, assignments, arguments, nested tuples, aliases,
  collection element types, and callable signatures;
- direct `CompareChain` construction by the parser for one or more operators;
- mixed operators, equality, membership, and chains in assertions,
  specifications, conditionals, and comprehension filters;
- generated lazy structure, including skipped later operands and single-use
  middle bindings;
- function and method calls without eager outer hoisting; and
- real mypy/Dafny validation of representative generated programs.

The implementation must pass the repository build and test targets, maintain
the existing coverage threshold, pass mutation-focused regression tests when
available, and pass the real-tool integration smoke test.
