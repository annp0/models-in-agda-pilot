## Abstract Specification

First we present the specs for our calculator model:

|   Spec #   | Concept                         | Description|
| :---: | ------------------------------- | ------------------------------------------------------------------------------------------------------------------------- |
| **1** | **Primitive & Composite Types** | Four primitives (`text`, `real`, `integer`, `boolean`) and one constructor for structured types (`vector : Type → Type`). |
| **2** | **Symbols**                     | Each symbol has a `name : String` and a `type : Type`.                                                                    |
| **3** | **Literal Values**              | Canonical typed literals, each indexed by the type they inhabit (`LiteralValue typ`).                                     |
| **4** | **Environment**                 | A list (`List Entry`) of symbol–value pairs where each binding carries its own proof of type correctness.                 |
| **5** | **Operators**                   | Typed unary and binary operators (`UnaryOp t₁ t₂`, `BinaryOp t₁ t₂ t₃`) defining legal type combinations.                 |
| **6** | **Expressions**                 | Typed abstract syntax tree, indexed by both the environment and its result type: `Expression env typ`.                    |
| **7** | **Evaluation**                  | Total and type-preserving functions `evalUnaryOp`, `evalBinaryOp`, and `evaluate`.                                        |

---

## Comparison

| **Spec #**                           | **Agda**                                                                                                                             | **Epsilon**                                                                                                 | **Similarities / Differences / Reasons**                                                                                                                                                               |                                                                                                                                                                                                                                                                |
| :----------------------------------- | :--------------------------------------------------------------------------------------------------------------------------------------------------- | :---------------------------------------------------------------------------------------------------------------------------- | :----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **1 – Type System**                  | `data PrimitiveType`; `data Type = base PrimitiveType vector Type`.                                                         | `enum Primitive`; `class PrimitiveType`; `class VectorType`; `class InvalidType`. Type relationships and arithmetic properties encoded in EOL (`isNumericTy`, `equiv`).                                | *Similarity*: both define base and vector type hierarchies.  <br>*Difference*: Agda enforces validity intrinsically, whereas Epsilon includes an `InvalidType` for runtime error propagation.  <br>*Reason*: dependent typing vs post-construction validation. |
| **2 – Symbols**                      | `record Symbol where { name ; type }` a record; uniqueness and naming are decidable externally.                                               | `class Symbol` with linked `SymbolDeclaration` objects. EVL enforces unique names and at least one input/output symbol.       | *Similarity*: both bind a name to a type.  <br>*Difference*: Agda symbols are immutable data; Epsilon symbols are mutable model elements subject to validation.                                        |                                                                                                                                                                                                                                                                |
| **3 – Literal Values**               | `data LiteralValue : Type → Set`                                                  | `TextLiteral`, `RealLiteral`, `IntegerLiteral`, `BooleanLiteral` classes with dynamic `type()` inference.                     | *Similarity*: one literal per primitive type.  <br>*Difference*: Agda guarantees type coherence by construction; Epsilon relies on `Expression.type()` and runtime checks.                             |                                                                                                                                                                                                                                                                |
| **4 – Environment / Entries**        | `Entry = Σ Symbol (λ s → LiteralValue (Symbol.type s))`; `Environment = List Entry`. Every entry is type-correct.                                    | Runtime `Map` from symbol name to value. Typing verified by constraint `astep.symbol.type.equiv(astep.body.type())`.          | *Similarity*: both provide a mapping from symbols to current values.  <br>*Difference*: Agda encodes correctness statically via dependent pairs; Epsilon performs dynamic validation.                  |                                                                                                                                                                                                                                                                |
| **5 – Operators**                    | `UnaryOp t₁ t₂` and `BinaryOp t₁ t₂ t₃` parameterized by operand and result types.                                                                   | Enum types `UnaryOp`, `BinaryOp`; semantics implemented in EOL.                                                               | *Similarity*: equivalent operator sets (`add`, `subtract`, `multiply`, `divide`, `negate`, `flip`).  <br>*Difference*: Agda encodes typing at construction; Epsilon checks compatibility procedurally. |                                                                                                                                                                                                                                                                |
| **6 – Expressions**                  | `Expression env typ` defines expressions typed by environment and result type. Constructors: `literal`, `symbolRef`, `unaryExpr`, `binaryExpr`. | `abstract class Expression` with subclasses (`TextLiteral`, `SymbolExpression`, `UnaryExpression`, etc.) and `type()` method. | *Similarity*: identical structural forms.  <br>*Difference*: Agda’s type index ensures only well-typed expressions exist; Epsilon validates well-typedness via EVL `WellTyped` constraint.             |                                                                                                                                                                                                                                                                |
| **7 – Evaluation**                   | `evaluate : Expression env typ → LiteralValue typ` is total and type-preserving.                                                                     | `evaluate(scope)` in EOL evaluates at runtime, returning `Any`.                                                               | *Similarity*: both compute the value of an expression recursively.  <br>*Difference*: Agda’s evaluator is total by type; Epsilon’s may fail on ill-typed or uninitialized symbols.                     |                                                                                                                                                                                                                                                                |
| **8 – Scoping & Dependencies**       | `symbolRef entry ∈ env` encodes proof of symbol availability.                                                                                        | `checkStepDependencies()` iterates through program steps to ensure dependency order.                                          | *Similarity*: both ensure no use-before-definition.  <br>*Difference*: Agda proves scoping statically; Epsilon checks it dynamically.                                                                  |                                                                                                                                                                                                                                                                |
| **9 – Validation / Well-Formedness** | Embedded directly in the type system; ill-formed constructs cannot be represented.                                                                   | Validation layer implemented in EVL (e.g., `WellTyped`, `AllStepsDepsHaveValues`, `UniqueSymbols`).                           | *Similarity*: both achieve well-formedness.  <br>*Difference*: Agda enforces by construction; Epsilon detects via separate validation phase.                                                           |                                                                                                                                                                                                                                                             

## Discussion

### Structural Accuracy

The Agda model captures a closed and minimal calculus for arithmetic  evaluation. All typing, scoping, and evaluation properties are enforced by the type system. The Epsilon model implements the same structure operationally but depends on runtime validation and external constraints.

### Predictiveness and Soundness

The Agda semantics are sound by construction; if it type-checks, it evaluates safely. In contrast, the Epsilon implementation achieves conditional soundness—correctness is assured only after all EVL constraints pass.

### Expressiveness and Practicality

Epsilon provides a practical environment for model editing, validation, and code generation (e.g., README and Java artifacts). Agda offers machine-checked proofs of semantic properties but lacks direct integration with model tooling.

### Governance Model

* Agda: Closed World (By Construction), every construct must be well-typed and scoped before it can exist. Ill-formed expressions are unrepresentable.
* Epsilon: Open World (Validate After Construction), Models can exist in transiently invalid states; correctness is recovered through validation passes.


## Conclusion

The Agda and Epsilon implementations of the Calculator model represent two complementary approaches to formal modeling:

* **Agda:** Defines the semantics, typing, and evaluation rules of the calculator within a total proof-carrying framework. Every construct is correct by design with mathematical soundness.

* **Epsilon:** Provides a flexible, operational framework that extends the same concepts to executable models, validation workflows, and code generation pipelines. Correctness is ensured by declarative constraints rather than type-checking.

They demonstrate how type theory and model-driven engineering can describe and enforce the same abstract computational structure from different vantage points. The Agda specification offers formal rigor suitable for verification and reasoning, while the Epsilon system delivers practical tooling.

