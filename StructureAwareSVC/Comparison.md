## The Model

From a high-level viewpoint, a **structure-aware version control system** can be understood through three complementary components:

* **Basic Structure**: the data objects and their internal relationships.
* **Operations**: the actions performed on those objects to detect or apply changes.
* **Guarantees**: the logical rules that must always hold before and after these actions.

### Basic Structure

1. **Trees.**
   The system operates on binary trees. Each node carries a value and up to two children: a left and a right subtree.


2. **Patches.**
   A *patch* represents a single edit that transforms one tree (the *source*) into another (the *target*).
   There are four distinct kinds of patches:

   * **No Change (NO_CHANGE)**: the two subtrees are identical.
   * **Insert (INSERT)**: a new subtree is introduced.
   * **Delete (DELETE)**: a subtree is removed.
   * **Modify (MODIFY)**: something within the node changes; this may include a new value, new children, or both.

   Patches may contain sub-patches for the left and right branches, allowing nested edits to be represented recursively.

3. **Positions and Locality.**
   Every patch applies to a specific *position* in the tree. For instance, at the root, at the left child of a node, or further down the hierarchy.
   The model does not use explicit identifiers or indices: position is determined structurally by where the patch is placed within the recursive tree.

4. **Well-Formedness.**
   For a patch to be well-formed:

   * A modification keeps the node shape intact (the node continues to exist).
   * Insertions and deletions replace entire subtrees.
   * Each sub-patch acts only on its own subtree (left or right) and does not interfere with other branches.

   This ensures patches describe coherent and structurally valid changes.

### Operations

5. **Computing Differences (Diff).**
   The system must be able to compare two trees given a *source* and a *target*, and produce a patch that represents their difference.
   The diff operation identifies which nodes were inserted, deleted, or modified and constructs the smallest consistent set of edits needed to transform one into the other. It must be deterministic: given the same two trees, the same patch is always produced.

6. **Applying Changes (Apply).**
   The system must be able to apply a patch to a tree, producing a new tree that reflects the described change.
   Application respects the four patch kinds:

   * A *no-change* patch leaves the subtree untouched.
   * An *insert* replaces an empty position with a new subtree.
   * A *delete* removes the subtree entirely.
   * A *modify* updates the node’s value (if changed) and applies any nested sub-patches to its children.

   When a patch is well-formed, applying it must always succeed and produce a valid tree.

### Guarantees

7. **Round-Trip Property.**
    For any two trees *A* and *B*:
    If the system computes a patch *P = diff(A, B)* and applies it to *A*, the result must be identical to *B*.
    This defines the essential correctness of the model.

8. **Reflexivity.**
    Comparing a tree with itself must produce a patch that represents *no change*.
    This ensures the diff operation recognizes identity correctly.

9. **Localized Effects.**
    Patches must affect only the subtree they describe.
    No edit may change data outside its defined scope.
    Unaffected parts of the tree remain exactly as they were.

10. **Shape Consistency.**
    After applying any patch, the resulting structure must still be a valid binary tree.
    The operation must never produce malformed nodes or half-built trees.


### Summary of Specification

| **Abstract Concept**      | **Requirement in the Tree Model**                                                                                                     |
| ------------------------- | ------------------------------------------------------------------------------------------------------------------------------------- |
| **Tree structure**        | Binary tree with a node value and up to two child subtrees (left and right).                                                          |
| **Patch types**           | Four edit kinds: **NO_CHANGE**, **INSERT**, **DELETE**, **MODIFY**.                                                                   |
| **Nested edits**          | Patches may include sub-patches for left and right branches, allowing recursive representation of deeper changes.                     |
| **Position and locality** | Each patch applies to a specific position in the tree, determined structurally (not by IDs or indices).                               |
| **Well-formedness**       | Modifications preserve node shape; insertions/deletions replace entire subtrees; sub-patches act only on their own subtrees.          |
| **Diff operation**        | Compares a source and target tree; identifies inserts, deletes, and modifications; must be deterministic.                             |
| **Apply operation**       | Executes the patch on a tree: inserts create, deletes remove, modifies update values and children, no-change leaves structure intact. |
| **Round-trip guarantee**  | Applying `diff(A, B)` to `A` must yield `B`.                                                                                          |
| **Reflexivity**           | Diffing a tree against itself produces a “no change” patch.                                                                           |
| **Localized effects**     | Each patch only affects its own subtree; other parts remain unchanged.                                                                |
| **Shape consistency**     | Applying any well-formed patch yields a valid binary tree—no malformed or partial structures.                                         |
| **Determinism**           | Same input trees always produce the same patch; no heuristic or random variation.                                                     |

Below is the **spec-by-spec (1–11)** comparison written in the exact style you asked for (neutral prose, then separate **Java Implementation**, **Agda Implementation**, **Key Features**, a short **Comparison** table, and brief strengths/weaknesses). All Java details are faithful to your code; Agda points reference the Utrecht report.

## Comparison

### Spec 1 & 2: Entities and Types (Trees, Patches)

#### Java Implementation

* **Trees** are concrete binary nodes:

```java
public class TreeNode<T> {
    public T value;
    public TreeNode<T> left;
    public TreeNode<T> right;

    public TreeNode(T value, TreeNode<T> left, TreeNode<T> right) { ... }
    public TreeNode(T value) { this(value, null, null); }
}
```

This encodes a possibly-empty binary tree (empty branch = `null`). 

* **Patches** use a closed set of four tags with optional payloads:

```java
public class Patch<T> {
    public enum Type { NO_CHANGE, INSERT, DELETE, MODIFY }

    public final Type type;
    public final TreeNode<T> source;
    public final TreeNode<T> target;
    public final Patch<T> leftPatch;
    public final Patch<T> rightPatch;

    public Patch(Type type) { ... }                     // NO_CHANGE
    public Patch(Type type, TreeNode<T> s, TreeNode<T> t) { ... }          // INSERT/DELETE
    public Patch(Type type, TreeNode<T> s, TreeNode<T> t,
                 Patch<T> lp, Patch<T> rp) { ... }      // MODIFY
}
```

#### Agda Implementation

* **Trees** are an instance of a *regular (algebraic) tree type* in the paper’s generic universe; binary trees are treated as a specific regular datatype. (See Intro + generic setting.) 
* **Patches** are defined *generically* over the universe; for fixpoints (recursive trees), patches are lists of edit ops over the one-step shape (`F¹`), capturing insert, delete, and modify at the constructor level. (Serialization view; then edit over the serialized heads/children.) 

#### Key Features

1. Java fixes the four patch kinds via an `enum`; Agda derives them via constructors in a generic `Patch`/`TPatch` indexed by the type’s structure.
2. Java’s trees are a concrete `TreeNode<T>`; Agda’s trees live inside a universe of datatypes, enabling uniform definitions across many shapes.

#### Comparison

| Feature       | Java                                                              | Agda                                                                       |
| ------------- | ----------------------------------------------------------------- | -------------------------------------------------------------------------- |
| Tree encoding | Concrete `TreeNode<T>` with nullable children.                    | Regular-tree datatype in a generic universe.                               |
| Patch space   | `enum` {NO_CHANGE, INSERT, DELETE, MODIFY} + optional subpatches. | Algebraic constructors; list of edits over serialized one-step structure.  |
| Genericity    | Per-type class (binary trees only).                               | Fully generic across datatypes (lists, trees, etc.).                       |

**Strengths / Weaknesses**

* **Java:** Simple, explicit, easy to read; limited to this tree; no generic proofs.
* **Agda:** Uniform across many types; formally precise; more abstract to read.

---

### Spec 3: Positions and Locality

#### Java Implementation

A patch applies at a node; any `leftPatch` can only affect the left subtree and `rightPatch` the right subtree. Locality is purely **structural** (no IDs). This is enforced by the recursive fields on `Patch` and by how `apply` threads each branch separately.  

#### Agda Implementation

Edits are attached to the *head* and its *children* in the serialized one-step view; sub-edits descend only into their corresponding children. Locality by construction—only the appropriate branch is edited. 

#### Key Features

* Both systems use *position = path in the tree*, not node identifiers.
* Disjoint subpatches (left vs right) cannot overlap.

#### Comparison

| Aspect      | Java                                    | Agda                                          |
| ----------- | --------------------------------------- | --------------------------------------------- |
| Addressing  | Structural (root/left/right recursion). | Structural via head/children in the universe. |
| Non-overlap | Encoded by `leftPatch`/`rightPatch`.    | Encoded by typed edit constructors.           |

---

### Spec 4: Well-Formedness (WF) of Patches

#### Java Implementation

WF is by construction of `Patch` and respected by `apply`:

* `MODIFY` keeps a node at that position (rebuilds with the target value if provided).
* `INSERT`/`DELETE` replace whole subtrees.
* Sub-patches only apply to their side.
  `PatchApplicator.apply` enforces these cases exhaustively. 

#### Agda Implementation

WF is typed: ill-formed edits are unrepresentable (constructors fix where inserts/deletes/modifies can occur; fixpoint case uses list of edits over `F¹`). 

#### Comparison

| WF guarantee | Java                               | Agda                                          |
| ------------ | ---------------------------------- | --------------------------------------------- |
| Mechanism    | Coding discipline + total `apply`. | Types/constructors forbid ill-formed patches. |

### Spec 5: Computing Differences (Diff)

Both are rule-based, cost-blind, deterministic.

Java:

```java
public static <T> Patch<T> diff(TreeNode<T> t1, TreeNode<T> t2) {
    if (t1 == null && t2 == null) return new Patch<>(Patch.Type.NO_CHANGE);
    if (t1 == null) return new Patch<>(Patch.Type.INSERT, null, t2);
    if (t2 == null) return new Patch<>(Patch.Type.DELETE, t1, null);

    Patch<T> leftPatch = diff(t1.left, t2.left);
    Patch<T> rightPatch = diff(t1.right, t2.right);

    if (!t1.value.equals(t2.value)) {
        return new Patch<>(Patch.Type.MODIFY, t1, t2, leftPatch, rightPatch);
    } else if (leftPatch.type == Patch.Type.NO_CHANGE &&
               rightPatch.type == Patch.Type.NO_CHANGE) {
        return new Patch<>(Patch.Type.NO_CHANGE);
    } else {
        return new Patch<>(Patch.Type.MODIFY, t1, t2, leftPatch, rightPatch);
    }
}
```

Agda:

```agda
data Tree (A : Set) : Set where
  ∅   : Tree A
  ⟨_∥_∥_⟩ : A → Tree A → Tree A → Tree A

data Patch (A : Set) : Set where
  NoCh   : Patch A
  Ins    : Tree A → Patch A
  Del    : Patch A
  Mod    : A → Patch A → Patch A → Patch A

diff : ∀ {A} → Tree A → Tree A → Patch A
diff ∅ ∅ = NoCh
diff ∅ t = Ins t
diff s ∅ = Del
diff ⟨a ∥ l1 ∥ r1⟩ ⟨b ∥ l2 ∥ r2⟩ with diff l1 l2 | diff r1 r2
... | pl | pr with a ≟ b
... | yes _ with pl , pr
... | (NoCh , NoCh) = NoCh
... | _              = Mod a pl pr
... | no _            = Mod b pl pr
```

Notes:

  * Same four structural cases in both.
  * No scoring or search; decisions follow structure and equality only.
  * For equal values and unchanged children -> no-change; otherwise -> modify (or insert/delete when one side is empty).


### Spec 6: Applying Changes (Apply)

#### Java Implementation

`PatchApplicator.apply` handles all four kinds:

```java
switch (patch.type) {
  case NO_CHANGE: return new TreeNode<>(tree.value,
                        apply(p.leftPatch, tree.left),
                        apply(p.rightPatch, tree.right));
  case INSERT:    return reconstruct(p.target,
                        apply(p.leftPatch, null),
                        apply(p.rightPatch, null));
  case DELETE:    return null;
  case MODIFY:    ...
}
```

Always returns either `null` or a well-formed node; subpatches thread down only their side. 

#### Agda Implementation

`gapply` is partial in general (since deserializing can fail) but total on patches produced by `gdiff`; four cases mirror insert/delete/modify/no-change in the generic representation. 

#### Comparison

| Aspect   | Java                                          | Agda                                          |
| -------- | --------------------------------------------- | --------------------------------------------- |
| Totality | Total for these trees.                        | Total for patches produced by `gdiff`.        |
| Safety   | Enforced by exhaustive switch + constructors. | Enforced by the type-level proof obligations. |


### Spec 7: Round-Trip Property (Apply ∘ Diff)

#### Java Implementation

Empirically validated by JUnit tests over multiple scenarios (no change, value change, deeper insertion, leaf→node, combined, deletion):
`apply(diff(a,b), a) == b`. 

#### Agda Implementation

Formally proved: applying the diff computed between `s` and `t` to `s` produces `t` (for the generic setting). 

#### Comparison

| Evidence   | Java (tests)                         | Agda (proof)                       |
| ---------- | ------------------------------------ | ---------------------------------- |
| Round-trip | Multiple unit tests assert equality. | Universal proof for the algorithm. |


### Spec 8: Reflexivity (Diff a a = NO_CHANGE)

#### Java Implementation

Tested explicitly: `Diff.diff(x, x)` returns a `NO_CHANGE` patch; applying it preserves the tree’s value/shape. 

#### Agda Implementation

Reflexivity follows from the cost model and the definitions of `gdiff`/`gapply` (identity has zero cost and yields a no-op patch). 

#### Comparison

| Property    | Java               | Agda                     |
| ----------- | ------------------ | ------------------------ |
| Reflexivity | Verified by tests. | Proved from definitions. |


### Spec 9: Localized Effects (Non-interference)

#### Java Implementation

Left subpatch edits only `left`; right subpatch edits only `right`. Tests cover cases where only one side changes; the other remains identical. 

#### Agda Implementation

Sub-edits are typed to the corresponding child position; proofs rely on the head/children decomposition that forbids cross-branch interference. 

#### Comparison

| Aspect   | Java                                        | Agda                                            |
| -------- | ------------------------------------------- | ----------------------------------------------- |
| Locality | Encoded by `leftPatch`/`rightPatch` fields. | Encoded by position-indexed constructors/edits. |

### Spec 10: Shape Consistency (Result is a Valid Tree)

#### Java Implementation

`apply` *always* returns `null` or a fully constructed `TreeNode` whose children are themselves results of recursive `apply`. No malformed structures can escape. (Delete → `null`, otherwise a node.) 

#### Agda Implementation

Post-conditions are proved at the type level; results inhabit the same algebraic datatype; deserialization difficulties are handled in the generic account with `Maybe`, but `gdiff`-produced patches are known-good. 

#### Comparison

| Guarantee    | Java                             | Agda                         |
| ------------ | -------------------------------- | ---------------------------- |
| Valid result | Ensured by implementation cases. | Ensured by types and proofs. |

### Summary

| Spec #  | Concept                        | Java Implementation                                                                                                                        | Agda Implementation                                                                                                            |
| ------- | ------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------ |
| **1–2** | Trees and patches              | Concrete `TreeNode<T>` class with nullable branches; patches defined by enum {NO_CHANGE, INSERT, DELETE, MODIFY} and recursive subpatches. | Binary-tree datatype with explicit constructors for empty/node; patch datatype with four constructors and recursive structure. |
| **3**   | Positions and locality         | Locality determined structurally; left/right subpatches only affect corresponding subtrees.                                                | Recursive locality by construction; each patch acts on its position and children only.                                         |
| **4**   | Well-formedness                | Ensured by disciplined construction and by exhaustive `apply` rules.                                                                       | Guaranteed by type system; ill-formed patches are unrepresentable.                                                             |
| **5**   | Diff computation               | Rule-based, cost-blind, deterministic recursion comparing structure and values.                                                            | Same four structural cases, rule-based and deterministic by pattern matching.                                                  |
| **6**   | Apply operation                | Executes the four patch kinds; always yields `null` or a well-formed `TreeNode`.                                                           | Recursive `apply` mirrors same four cases; total on well-formed patches.                                                       |
| **7**   | Round-trip property            | Verified empirically: `apply(diff(a,b), a) == b`.                                                                                          | Proven formally: `apply (diff a b) a ≡ b`.                                                                                     |
| **8**   | Reflexivity                    | Tested: `diff(a,a)` yields NO_CHANGE patch.                                                                                                | Proven by structural induction.                                                                                                |
| **9**   | Localized effects              | Left/right edits are isolated; unaffected branches unchanged.                                                                              | Sub-edits typed to child position; non-interference proven.                                                                    |
| **10**  | Shape consistency              | `apply` always returns valid tree or `null`; never malformed.                                                                              | Post-conditions enforced by datatype; result always a valid tree.                                                              |
| **11**  | Determinism and inspectability | Pure rule set, no randomness; patch kind and scope visible via fields.                                                                     | Structural recursion, deterministic; change kind and scope visible by pattern matching.                                        |

## Reasons for Differences

* Paradigm. Java is an executable, object-oriented model emphasizing concrete data and procedural rules; Agda is a dependently typed, functional model emphasizing total functions and structural proofs.
* Verification. Java validates behavior empirically through tests, while Agda enforces it by construction and proof.
* Structure. Java’s representation is pragmatic where Trees and patches as mutable records, while Agda's is algebraic, embedding structure directly in the type system.
* Safety. In Java, correctness depends on disciplined coding and exhaustive case handling; in Agda, correctness is inherent in types and inductive definitions.
* Scope. Java targets one practical case (binary trees); Agda generalizes over arbitrary datatypes through a unified framework.

## Conclusion

Both implementations satisfy the same specifications through different idioms:

* The Java model provides a clear, operational realization of the patching semantics. It is simple, deterministic, and easily testable on real data.
* The Agda model expresses the same logic in a constructive setting. It is structurally precise, provably correct, and extensible to formal reasoning over more general datatypes.

Together they demonstrate two complementary views: Java for execution and verification by example, and Agda for formal assurance and proof of correctness.
