### Specification of the Abstract Model

This model defines a generic approach to version control that exploits the internal structure of data to track and manage changes more precisely than traditional line-based methods:

#### Concepts

- Data is represented as a tree. Our model is limited to binary trees only.
- Patches: A patch is a structured description of the transformation required to evolve one version of structured data into another. Types of transformations a patch can represent include:
    - `No Change`: Indicates that a particular part of the structure remains identical.
    - `Insert`: Represents the addition of a new structural element or an entire subtree.
    - `Delete`: Represents the removal of an existing structural element or an entire subtree.
    - `Modify`: Represents a change in the value of an element or a change within its substructure.

#### Operations

- `Diff`:
    - Takes two instances of structured data (a source and a target).
    - Compares their structures and values recursively.
    - Computes and returns a patch that, when applied to the source, transforms it into the target.

- `Apply`:
    * Takes a source instance of structured data and a patch.
    * Applies the transformations described in the patch to the source data.
    * Produces the transformed data instance (which should ideally match the target used in the diff operation).

#### Properties

- Consistency (Round-Trip Property): For any two structured data instances (trees) A and B, if patch_AB is the patch computed by applying the Diff function to A and B (i.e., patch_AB = Diff(A, B)), then applying patch_AB to A using the Apply function should precisely yield B (i.e., Apply(A, patch_AB) = B).

### Comparison and Language-Forced Design Choices

Both the Agda and Java models implement the core logic of structure-aware diffing and patching, but their underlying languages impose distinct design choices:

#### Genericity

The ability to write code that works with a wide variety of data types is a key aspect where Agda and Java demonstrate fundamentally different approaches due to their respective type systems.

##### Agda

Agda's dependent type system enables a level of generic programming that allows for uniform operations across diverse data structures, fundamentally rooted in the concept of "Regular Tree Types" (RTTs).


- Generic Trees: Agda defines a formal specification for RTTs. This is not just an interface but a way to describe the recursive structure of data types themselves. For example, a binary tree (`BTree`) and a list (`List`) can both be formally represented as instances of RTTs by defining how their "shape" can be serialized into a sequence of "heads" (values at the current node) and "children" (sub-structures). This unified description at the type level allows Agda to reason about the structural properties of different recursive types in a consistent manner.

- Generic Patches: The `TPatch` data type in Agda is defined generically as well, directly indexed by the RTT it applies to. This means the patch's structure inherently adapts to the specific data type it is intended to transform. For instance, the `Ins` (Insert) constructor of `TPatch` means "insert a subtree" when applied to a `BTree` context, but "insert an element" when applied to a `List` context. The underlying `TPatch` definition remains generic.

- Generic Diff and Apply Algorithms: The `diff` and `apply` algorithms themselves are defined once for all RTTs. They operate on the generic, formalized "shape" of the data. The conceptual mechanism involves "serializing" the structured data into a uniform representation (e.g., lists of heads and children) that the generic algorithms can process. After computing changes on this generic representation, the result is "deserialized" back into the specific target structured type. This eliminates the need to rewrite the core diffing and patching logic for every new data type.


##### Java

Java offers tools for genericity, but they operate at a different level and come with inherent limitations compared to Agda's dependent types.

- Templates: It provides parametric polymorphism, allowing classes (like `TreeNode<T>`, `Patch<T>`) and methods (like `Diff.diff<T>`) to operate on various types. This means you can create a `TreeNode<String>` or `TreeNode<Integer>`, and the compiler will ensure consistency. However, it does have its limitations:
    - Java generics cannot express a "universe" that captures the structural properties of arbitrary algebraic data types in the same way Agda's RTTs do. You can have `List<T>`, `Map<K,V>`, `TreeNode<T>`, but there isn't a common, expressive interface or abstract class that allows a single `diff` or `apply` method to generically understand and manipulate the internal recursive structure of all these disparate types.
    - Java generics are implemented with type erasure, where type parameters are removed at compile time. This means that at runtime, the generic type information is not available, limiting what can be done with types (e.g., you can't perform `instanceof` checks on generic types, or generically inspect the constructors of an arbitrary data type).
    - Java fundamentally lacks dependent types. This prevents type parameters from depending on values or expressing complex relationships between types in function signatures. For example, Agda can ensure, at compile-time, that a patch for a binary tree precisely matches and applies only to a binary tree. In Java, ensuring such precise structural consistency for arbitrary types often relies on runtime checks, careful design conventions, or explicit casting, which are less robust than compile-time guarantees.

- Abstract Classes / Interfaces: Abstract classes or interfaces can be used to establish common contracts or behavior. For instance, a `StructuredData` interface might have methods like `getChildren()` or `getValue()`. However, it is still limited:
    - Each concrete data structure (e.g., `BinaryTree`, `LinkedList`, `JsonNode`) would still need to explicitly implement these interfaces. Crucially, the detailed logic for "serializing" or "deserializing" the data into a generic form (which Agda's RTTs handle intrinsically) would need to be written specifically for each implementation.
    - While interfaces enforce a method contract, the actual interpretation of the structure often devolves to runtime dispatches (method calls on interface objects). This lacks the compile-time structural reasoning and optimization capabilities that Agda's dependent types offer.

#### Patch Representation and Semantics

- Agda defines `TPatch` as an algebraic data type, with distinct constructors for different types of changes (e.g., insertion, deletion, modification).

- Java defines `Patch` as a class with an `enum Type`. The `Patch` class encapsulates the type of change along with relevant `TreeNode` instances (source, target) and references to sub-patches (`leftPatch`, `rightPatch`).

#### Formal Verification vs. Testing

- Agda: Uses formal verification. Properties of the algorithms are prototyped and proven using Agda's type system. This approach establishes correctness through mathematical proof.

- Java: Uses unit testing. The `Test.java` file contains tests that validate the implementation against specific scenarios. This approach relies on executing code against predefined inputs to check for expected behavior.

### Summary

The Agda model presents a formally verified and generical structure-aware version control model. On the other hand, The Java model provides a practical OO implementation of the same model, relying on runtime checks and testing for correctness.