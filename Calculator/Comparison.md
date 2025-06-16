## Specifications

This specification outlines a structured model for defining and executing computations. We have:

- Symbols: A named data holder within a computation, each assigned a specific Type. 

- Type System: Defines the nature of data handled within the computation.
    - Primitive Types: Fundamental data kinds such as text, real numbers, integers, and booleans.
    - Structured Types: Collections of values (e.g., vectors) based on other types.

- Value: A concrete instance of a specific Type. This includes direct literal values (e.g., a specific number, text string, or boolean truth value).

- Expression: A formula that, when evaluated within a given context, yields a value of a predetermined type. Expressions can be:
    - Literal Values: Directly embedded constant values.
    - Variable References: Pointers to the current Value of a declared Variable.
    - Unary Operations: Computations on a single Expression.
    - Binary Operations: Computations combining two Expressions.

- Evaluation Context: The dynamic mapping of symbols to their current values, representing the state during computation.

## Comparison

- Type System & Guarantees:
    - Eclipse: Uses a fixed metamodel (e.g., Ecore) for structural typing, with behavioral logic and validation rules expressed separately (e.g., EOL, EVL). `Expression.type()` determines runtime type. `WellTyped` constraint and `AllStepsDepsHaveValues` constraint enforce correctness post-construction via external validation. Permits construction of potentially invalid models, with errors detected in a separate validation phase.
    - Agda: Uses a dependently-typed system where types can parameterize terms (e.g., `Expression env typ`). This allows embedding properties like symbol existence (`entry ∈ env`) directly into type signatures. Ill-formed constructs are unrepresentable by construction.

- Handling of Constraints/Validation:
    - Eclipse: Relies on external declarative constraint languages (EVL) and operational checks (EOL) to define well-formedness rules. These are applied in a distinct validation step, outside the metamodel definition.
    - Agda: Type constructors and function signatures inherently encode many constraints. For instance, the type signature of `BinaryOp` directly dictates valid operand and result types.

- Mutability
    - Eclipse: Typically operates on mutable model instances, allowing in-place modification of object attributes and references, characteristic of object-oriented modeling frameworks.
    - Agda: Primarily uses immutable algebraic data types and records. Operations (e.g., `evaluate`) take existing values as input and yield new values as output.