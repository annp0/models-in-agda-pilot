## Abstract Model

A file system is a structured method for organizing, storing, and managing files on storage devices such as hard drives, SSDs, and USB drives. [1](https://en.wikipedia.org/wiki/File_system)

### Key Components of a File System

* **Objects**: At the most abstract level, a file system consists of a finite set of objects. Following Silberschatz et al. (*Operating System Concepts*, 9th ed., Ch. 11), these objects are either files or directories, with a distinguished root directory that forms the entry point of the hierarchy. Each object must be uniquely identifiable and comparable for equality; we assume this equality is decidable, as required for operations such as parent lookup and removal.

* **Directories**: A directory provides containment and namespace management. In line with Silberschatz (Ch. 11.2), every non-root object belongs to exactly one directory (its parent), and directories can hold an arbitrary number of child objects. The root directory is itself a directory object with no parent.

* **Hierarchy and Containment Relation**: The objects form a rooted tree under a contained-in relation. Silberschatz (Ch. 11.2) describes this as the parent–child mapping between directories and files. This relation must satisfy preorder properties (reflexivity and transitivity) to ensure consistency of traversal and containment.

* **Metadata / Information**: Each object carries some information (metadata or status). Following Silberschatz (Ch. 11.3), metadata such as file type, timestamps, or access control information is conceptually attached to the object. In our abstract view this is a general "Info" field, so that different systems may instantiate it with richer status if desired.

* **Distinction Between Files and Directories**: Whether an object is a directory must be decidable (Silberschatz, Ch. 11.2). This distinction allows us to enforce that only directories may contain children and that the root is always a directory.

### Supported Operations

* **Retrieving Information**: Given an object, one can retrieve its associated information (Silberschatz, Ch. 11.2 “File Attributes”), which stands for both data contents and metadata.

* **Enumerating Children and Parents**: Because directories form the backbone of the hierarchy, we must be able to (a) enumerate the children of any directory object together with proofs that they are indeed children, and (b) obtain the parent of any non-root object. This mirrors the directory traversal operations described in Silberschatz (Ch. 11.2).

* **Removing Objects**: Any non-root object may be removed, producing a new file system. Silberschatz (Ch. 11.3) stresses that file systems must ensure such deletions only affect the targeted subtree and leave unrelated objects intact.

* **Adding Objects**: A new subtree can be added under any directory object, again yielding a new file system. This operation generalizes file creation and directory creation in Silberschatz (Ch. 11.2–11.3), and we require that objects not in the modified subtree are mapped to new objects whose information is unchanged.

* **Localized Effects Guarantee**: Both removal and addition must satisfy a localized-effect property: if an object is not contained in the area being modified, its information remains identical after the operation. This property captures Silberschatz's emphasis on isolation of changes and consistency of directory trees.

## The Model

From the textbook view (Silberschatz et al., *Operating System Concepts*, 9th ed., Ch. 11), a file system can be abstracted by three interlocking parts:

* **Basic Structure**: the static shape of objects, directories, and their containment relation.
* **Operations**: adding, moving, and deleting objects.
* **Guarantees**: correctness and localized side effects of those operations.

This section specifies what our abstract model of a file system must satisfy before any implementation.

### Basic Structure

1. **Objects (Files and Directories).**
  The file system consists of a finite set of live objects. Each object is either a file or a directory.

2. **Root Directory.**
  There is a single distinguished root directory. The root has no parent and is always a directory object. Whether an object is the root must be decidable, ensuring a clear entry point to the hierarchy.

3. **Parent–Child Relation.**
  Each non-root object has exactly one parent directory, and each directory may contain zero or more child objects. This forms a rooted tree under a “contained-in” relation satisfying preorder properties (reflexivity and transitivity), consistent with Silberschatz (Ch. 11.2).

4. **Metadata / Information.**
  Each object has associated “information” — a placeholder for contents, attributes, or status. Silberschatz (Ch. 11.3 “File Attributes”) lists timestamps, permissions, and file type as examples. Our abstract model only assumes an information field without constraining its structure.

5. **File vs. Directory Predicate.**
  Whether an object is a directory must be decidable. Only directories may have children, and the root is always a directory.

### Operations

6. **Retrieving Information.**
  Given any object, the model must provide a way to extract its information (metadata or status).

7. **Navigating the Hierarchy.**
  The model must support querying the children of any directory and the parent of any non-root object.

8. **Adding and Removing Objects.**
  The model must allow insertion of a new subtree under any directory and removal of any non-root object.

### Guarantees

9. **Localized Effects.**
  Operations must affect only the targeted objects or subtrees. If an object is outside the subtree being modified, its information must remain unchanged. This reflects Silberschatz’s consistency requirements (Ch. 11.3 “Consistency Semantics”).

10. **Consistency of the Hierarchy.**
  After any operation, the resulting structure must still satisfy the Basic Structure conditions (unique root, well-formed parent–child relations, decidable directory predicate).

### Summary of Specification

| **Abstract Concept (from textbooks)** | **Requirement in the Model**                                 |
| ------------------------------------- | ------------------------------------------------------------ |
| Files and directories                 | Two object types with decidable classification               |
| Root directory                        | Unique, directory, no parent, decidable "is-root"            |
| Parent–child hierarchy                | Preorder "contained-in" relation, each non-root has a parent |
| Metadata                              | Each object carries information retrievable by a function    |
| Adding / removing                     | Must be possible while preserving hierarchy                  |
| Localized effects                     | Unaffected objects keep identical information                |


### Features and Characteristics

This paper [2](https://inria.hal.science/inria-00538459/document) has identified the following features & characteristics that a good model should follow:

Features:
- **Mapping Feature**: A model is based on an original.
- **Reduction Feature**: A model only reflects a relevant selection of an original's properties.
- **Pragmatic Feature**: A model needs to be usable in place of an original with respect to some purpose.

Characteristics:
- **Abstraction**: A model is always a reduced rendering of the system that it
represents.
- **Understandability**: A model must remain in a form that directly appeals to our intuition.
- **Accuracy**: A model must provide a true-to-life representation of the modeled system's features of interest.
- **Predictiveness**: A model must correctly predict the interesting but non-obvious properties of the modeled system.
- **Inexpensiveness**: A model must be significantly cheaper to construct and
analyze than the modeled system.

We check our model against those points. As for features:

- **Mapping Feature**: The model is based on common understandings of file systems as described by Wikipedia and other sources, which is our original. 
- **Reduction Feature**: We have abstracted away certain elements from the original description:
    - **Pathnames**: Existing file systems usually separate the notion of files / directories themselves and their pathnames. We find this to be unnecessary: pathnames are used as unique identifiers, but when we talk about different objects in a modeling language, we are already identifying them in some way. Therefore we didn't explicitly define path names in our model.
    - **Metadata**: We can just include them as the information contained in files / directories.
    - **Storage Allocation etc.**: This aspect is ignored since the physical storage details are not the focus of our model.
- **Pragmatic Feature**: The model retains the essential features of a file system: the APIs of our model have given ways to extract the information in files, provide all access to the file system structure, and to modify the system by adding / removing objects. This can be use in place of the original.

As for characteristics:

- **Abstraction**: By the reduction feature and pragmatic feature, we can conclude that our model has abstracted away certain elements from the original description while preserving its essential features.
- **Understandability**: The model appeals to our intuition by using the tree hierarchy. We excluded the approach of modeling file systems as graphs and so on because they are less intuitive.
- **Accuracy**: Compared to real world file systems (e.g., NTFS, ext4), the model is accurate from the following perspectives:
    - Each non-root object has a single parent, and directories can have multiple children.
    - The root is unique, and it is decidable.
    - Every file or directory, except the root, must be contained within a directory, and directories can hold multiple items.
- **Predictiveness**: The model specifies properties that are crucial for a predictable file system, for example:
    - Parent-Child consistency.
    - Operations only have localized and predictable effects: the model ensures that operations such as adding or removing files or directories only affect the targeted objects and their immediate relationships.
- **Inexpensiveness**: Implementing this model in a modeling language is significantly simpler than developing a real file system since detailed aspects like metadata and storage allocation are not considered.

## Our Agda Model

In this section, we show how the abstract specification (items 1 – 10) is implemented in Agda.

### Basic Setup

We model a file system as a predicate on some arbitrary object `A` that contains APIs as described in our speculation:

```agda
record IsFS (A : Set) : Set₁ where
```

* **Spec 1 (Objects):** `FSObj : A → Set` introduces the universe of live objects, which will be either files or directories.
* **Spec 4 (Metadata):** `Info : Set` stands for per-object information such as contents, attributes, or status.

```agda
FSObj : A → Set
Info  : Set
```

* **Spec 2 (Root Directory):** `root : ∀ {a : A} → FSObj a` establishes a unique root object. Decidability of “is root” follows from decidable equality:

```agda
_≡ᵒ_  : ∀ {a} → FSObj a → FSObj a → Set
≡ᵒ-prop : ∀ {a} → IsEquivalence (_≡ᵒ_ {a})
_≡ᵒ?_ : ∀ {a} (obj₁ obj₂ : FSObj a) → Dec (obj₁ ≡ᵒ obj₂)

IsNotRoot  : ∀ {a} → FSObj a → Set
IsNotRoot? : ∀ {a} (obj : FSObj a) → Dec (IsNotRoot obj)
```

* **Spec 2 (root must be decidable)** -> `IsNotRoot` and `_≡ᵒ?_`.
* **Spec 3 (unique root directory)** -> `root` + `RootIsDir` below.

### Hierarchy Structure

This part realizes Spec 3 (Parent–Child Relation) and Spec 5 (Directory Predicate):

```agda
IsDir : ∀ {a} → FSObj a → Set
IsDir? : ∀ {a} → (obj : FSObj a) → Dec (IsDir obj)
RootIsDir : ∀ (a : A) → IsDir (root {a})
```

* **Spec 5 (File vs Directory):** `IsDir` is a decidable predicate separating directories from files; `RootIsDir` enforces that the root is always a directory.

We then formalize the parent–child relation:

```agda
IsChild : ∀ {a} → FSObj a → FSObj a → Set
IsChild-IsDir : ∀ {a} {par kid : FSObj a} → IsChild par kid → IsDir par

get-children : ∀ {a} → (obj : FSObj a) → IsDir obj 
            → List (Σ[ kid ∈ (FSObj a) ] IsChild obj kid)

get-parent : ∀ {a} → (obj : FSObj a) → IsNotRoot obj
    → Σ[ par ∈ (FSObj a) ] IsChild par obj
```

* **Spec 3:** `get-children` returns all children plus proofs they are children; `get-parent` retrieves a parent together with the child proof. `IsChild-IsDir` enforces valid relations.

### Operations

These definitions implement Spec 8 (Adding / Removing Objects):

```agda
remObj : ∀ {a} → (obj : FSObj a) → IsNotRoot obj → A
addFS  : ∀ {a} → (obj : FSObj a) → IsDir obj → A → A
```

* **Spec 8:** `remObj` removes any non-root object; `addFS` inserts a new subtree under a directory; (moving can be defined as remove+add).

### Guarantees (Side Effects)

This part implements Spec 9–10 ("Localized Effects" and "Consistency of the Hierarchy").

```agda
_≤ᵒ_ : ∀ {a} → FSObj a → FSObj a → Set
≤ᵒ-prop : ∀ {a} → IsPreorder (_≡ᵒ_ {a}) (_≤ᵒ_ {a})
_≰ᵒ_ : ∀ {a} → FSObj a → FSObj a → Set
_≰ᵒ_ obj₁ obj₂ = ¬ (obj₁ ≤ᵒ obj₂)
```

* **Spec 3 (Hierarchy as preorder):** `_≤ᵒ_` is the containment relation satisfying preorder properties.

To enforce **localized effects** we define mapping functions:

```agda
rem-map : ∀ {a} → (objr : FSObj a) → (nr : IsNotRoot objr) 
    → (objo : FSObj a) → objr ≰ᵒ objo
    → Σ[ objn ∈ FSObj (remObj objr nr) ] extract objo ≡ extract objn

add-map : ∀ {a} → (objm : FSObj a) → (idom : IsDir objm) 
    → (objo : FSObj a) → objo ≰ᵒ objm → (b : A)
    → Σ[ objn ∈ FSObj (addFS objm idom b) ] extract objo ≡ extract objn
```

* **Spec 9 (Localized Effects):** If an object lies outside the modified subtree, its information (`extract`) is unchanged.
* **Spec 10 (Hierarchy Consistency):** Both `rem-map` and `add-map` return objects in the new file system, proving the resulting hierarchy remains well-formed.

| **Specification**         | **Agda Construct**                                         |
| ------------------------------------- | ---------------------------------------------------------- |
| 1–2 Objects, root                     | `FSObj`, `root`, `_≡ᵒ?_`, `IsNotRoot?`                     |
| 3 Parent–child hierarchy              | `IsChild`, `get-parent`, `get-children`, `_≤ᵒ_`, `≤ᵒ-prop` |
| 4/6 Metadata / Information              | `Info`, `extract`                                          |
| 5 Directory predicate                 | `IsDir`, `IsDir?`, `RootIsDir`                             |
| 7 Navigating the hierarchy    | `get-parent`, `get-children`   |
| 8 Add/Remove       | `addFS` `remObj` |
| 9-10 Localized Effects / Consistency | `add-map`, `rem-map`, `_≰ᵒ_`                               |


### Conclusion

This model is clearly a type theory model. As noted in [2](https://www.cse.chalmers.se/~patrikj/papers/TypeTheory4ModProg_preprint_2018-05-19.pdf), type theory models satisfy typical modeling needs, and our model confirms this:

- **Expressiveness**: Agda effectively models the structure of file systems.
- **Properties**: Properties like `IsChild` and `add-map` can be expressed as dependent-type-valued functions, which also serve as proofs. This is advantageous for reasoning since we don’t need to extract proofs from properties as with traditional boolean-valued predicates.
- **Analysis**: The type-checking process is automatic. Once the code type checks, we can say that all the results we have proven in this model is mathematically sound.

However, we identified several limitations:

- **Visualization**: There is no straightforward way to visualize a type theory model.
- **Automated Reasoning**: Proofs for every property must be manually provided, which is time-consuming and challenging. Automated reasoning would be beneficial, but Agda does not support even proving basic results automatically.

## The Alloy Model

We now present a relational-logic instantiation of the same abstract specification, expressed in Alloy. Where the Agda model uses dependent types and proofs, Alloy uses sets and relations.

### Basic Setup

```alloy
abstract sig FSObject { }
sig File, Dir extends FSObject { }
```

* **Spec 1 (Objects):** `FSObject` defines the universe of file system objects.
* **Spec 5 (Directory Predicate):** Alloy uses sub-signatures instead of a predicate. Only `Dir` can occur in directory fields.

```alloy
sig FileSystem {
  live: set FSObject,
  root: Dir & live,
  parent: (live - root) ->one (Dir & live),
  contents: Dir -> FSObject
}{
  // Spec 3c: all live objects reachable from root
  live in root.*contents

  // Spec 3: parent and contents are inverses
  parent = ~contents
}
```

* **Spec 2 (Root Directory):** `root: Dir & live` ensures a single root directory in the live set.
* **Spec 3 (Parent–Child Hierarchy):** `parent` and `contents` capture the containment relation, and `parent=~contents` enforces inverse consistency.
* **Spec 3c (Reachability):** `live in root.*contents` guarantees every live object is reachable from root.
* **Spec 4 (Metadata):** Metadata remains abstract; in Alloy we could add attributes as additional fields but omit them here.

### Operations

We implement the operations demanded by Specs 6–8 (retrieving, adding, and removing). Retrieval of children and parent is naturally expressed by Alloy relational queries; adding and removing are encoded as predicates over old/new states.

#### Adding Objects

```alloy
pred add [fs, fs': FileSystem, newObj: FSObject, targetDir: Dir] {
  // Spec 8: target directory must exist, newObj must be fresh
  targetDir in fs.live
  newObj not in fs.live

  // Spec 8: extend live set
  fs'.live = fs.live + newObj

  // Spec 3: update parent relation to link newObj to targetDir
  fs'.parent = fs.parent + newObj->targetDir

  // Spec 3: update contents accordingly
  fs'.contents = fs.contents ++ targetDir->newObj
}
```

* **Spec 8 (Adding):** Inserts a new object under `targetDir`.
* **Spec 9 (Localized Effects):** All other relations stay the same.

#### Removing Objects

```alloy
pred remove [fs, fs': FileSystem, x: FSObject] {
  // Spec 8: only non-root objects can be removed
  x in (fs.live - fs.root)

  // Spec 8: shrink live set
  fs'.live = fs.live - x

  // Spec 3: remove the parent mapping for x
  fs'.parent = fs.parent - x->(x.(fs.parent))

  // Spec 3: remove contents mapping
  fs'.contents = fs.contents - (x.~fs.parent->x)
}
```

* **Spec 8 (Removing):** Removes a single object from the file system, preserving the hierarchy for all others.
* **Spec 9 (Localized Effects):** Objects outside the deleted subtree retain their parent and contents.

### Guarantees (Correctness Checks)

We then use Alloy’s `check` assertions to verify the guarantees of Specs 9–10.

```alloy
addOkay: check {
  all fs, fs': FileSystem, newObj: FSObject, d: Dir |
    add[fs, fs', newObj, d] => fs'.live = fs.live + newObj
} for 5
```

* **Spec 9/10:** Checks that adding an object extends the live set exactly as specified.

```alloy
removeOkay: check {
  all fs, fs': FileSystem, x: FSObject |
    remove[fs, fs', x] => fs'.live = fs.live - x
} for 5
```

* **Spec 9/10:** Checks that removing an object removes exactly that object from the live set.

### Summary

| **Specification Item (1–10)** | **Alloy Construct**                                    |
| ----------------------------- | ------------------------------------------------------ |
| 1–2 Objects, root             | `FSObject`, `File`, `Dir`, `root: Dir & live`          |
| 3 Parent–child hierarchy      | `parent`, `contents`, `parent=~contents`, reachability |
| 4 Metadata / Information      | (extendable attributes)                                |
| 5 Directory predicate         | `Dir` signature                                        |
| 6–7 Retrieving and Navigating | Alloy relational queries over `parent`/`contents`      |
| 8 Add / Remove                | `pred add`, `pred remove`                              |
| 9 Localized Effects           | `addOkay` and `removeOkay` checks                      |
| 10 Consistency of hierarchy   | Invariant in `sig FileSystem` plus checks              |

### Conclusion

This Alloy model gives a relational-logic view of our abstract file system specification.

* **Expressiveness**: Objects, directories, and hierarchy are captured as sets and relations.
* **Properties**: Alloy’s SAT-based `check`s automatically explore finite scopes to verify the localized effects of operations.
* **Limitations**: Alloy covers only finite instances and requires manual predicates for operations like move or recursive removal, but it excels at automated counterexample search and visualization.


## Comparison between the Alloy Model and our Agda model

| **Spec # / Feature**                                  | **Agda Model Implementation**                                                                            | **Alloy Model Implementation**                                                                                                                   | **Similarities (Both)**                                                                         | **Differences**                                                                                                                                    | **Reasons for Differences**                                                                                                         |
| ----------------------------------------------------- | -------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------ | ----------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------- |
| **1. Objects (Files & Directories)**                  | `FSObj : A → Set` defines universe of objects. File/Dir distinction via `IsDir` predicate.               | `abstract sig FSObject { }` then `sig File, Dir extends FSObject` (two sub-signatures).                                                          | Both define a universe of file system objects, distinguishing files and directories.            | Agda uses a single type with predicates; Alloy uses disjoint sub-signatures.                                                                       | Type theory encourages a uniform type with proofs attached; Alloy’s relational logic uses signature hierarchy for classification.   |
| **2. Root Directory**                                 | `root : ∀ {a} → FSObj a`, plus `IsNotRoot`/`IsNotRoot?` for decidability.                                | `root: Dir & live` in `sig FileSystem`.                                                                                                          | Both ensure a unique, distinguished root directory that is a directory.                         | Agda enforces decidability and uniqueness via explicit proofs; Alloy enforces via field constraints and scope checking.                            | Dependent types require explicit decidable predicates; Alloy automatically enforces constraints in finite scope.                    |
| **3. Parent–Child Relation / Hierarchy**              | `IsChild`, `get-parent`, `get-children` plus preorder `_≤ᵒ_` and `≤ᵒ-prop`.                              | `parent` and `contents` relations; `parent = ~contents`; reachability `live in root.*contents`.                                                  | Both encode a rooted tree hierarchy; both allow navigation from parent to child and vice versa. | Agda requires explicit preorder proofs and functions returning Σ-types; Alloy encodes inverse relations and uses transitive closure automatically. | Constructive type theory must encode closure properties and proofs; Alloy’s logic natively supports relational closure.             |
| **4. Metadata / Information**                         | `Info : Set` plus `extract : FSObj a → Info`.                                                            | Metadata left abstract, but extendable as additional fields in `sig FileSystem` or `sig FSObject`.                                               | Both attach per-object “information” conceptually.                                              | Agda’s Info is a formal type parameter enforced everywhere; Alloy’s attributes are optional and untyped atoms.                                     | Dependent typing vs. untyped relational atoms: Agda must parameterize and prove correctness; Alloy leaves attributes flexible.      |
| **5. File vs Directory Predicate**                    | `IsDir` predicate and `IsDir?` decidable, plus `RootIsDir`.                                              | `Dir` signature (subclass of FSObject).                                                                                                          | Both separate directories from files and ensure only directories have children.                 | Agda uses predicates; Alloy uses two signatures.                                                                                                   | Same reason as Spec 1 — dependent types vs. relational signatures.                                                                  |
| **6. Retrieving Information**                         | `extract : FSObj a → Info` returns information for any object.                                           | In Alloy, retrieval is just querying fields or attributes of `FSObject` directly.                                                                | Both support information retrieval.                                                             | Agda uses an explicit total function; Alloy uses implicit relational queries.                                                                      | In type theory, everything must be explicitly a function with a type; Alloy’s relational logic allows direct selection by relation. |
| **7. Navigating the Hierarchy (Parent/Children)**     | `get-children` (returns list of children with proofs), `get-parent` (returns parent with proof).         | Alloy queries: `fs.contents[d]` to list children; `fs.parent[x]` to find parent.                                                                 | Both provide navigation primitives consistent with the hierarchy.                               | Agda returns dependent pairs requiring proofs; Alloy returns sets with no proofs.                                                                  | Again, constructive vs. relational paradigms.                                                                                       |
| **8. Adding and Removing Objects**                    | `addFS : FSObj a → IsDir obj → A → A` to add; `remObj : FSObj a → IsNotRoot obj → A` to remove.          | `pred add [fs, fs', newObj, targetDir]` and `pred remove [fs, fs', x]`.                                                                          | Both can add a new object under a directory and remove any non-root object.                     | Agda’s functions must return a new `A` with well-typed FSObj; Alloy’s predicates specify new relations over `fs'`.                                 | Agda constructs the new state as a function with proofs; Alloy constrains a new state and lets the SAT solver find models.          |
| **9. Localized Effects Guarantee**                    | `add-map` and `rem-map` proofs: show unchanged objects keep same `extract`.                              | `check addOkay` and `check removeOkay` assert that live sets are updated exactly and no other unintended changes occur.                          | Both ensure operations only affect targeted subtrees.                                           | Agda proves properties constructively inside the type; Alloy searches finite scope for counterexamples.                                            | Constructive proofs vs. automated counterexample checking (different verification philosophy).                   |
| **10. Consistency of the Hierarchy After Operations** | Preorder `_≤ᵒ_` maintained; `add-map` and `rem-map` produce objects in the new FS preserving invariants. | `parent = ~contents` and reachability constraints in `sig FileSystem` automatically enforced for each `fs'`; Alloy checks them after operations. | Both guarantee hierarchy integrity after add/remove.                                            | Agda encodes consistency as types/proofs; Alloy encodes as global invariants + checks.                                                             | Again, type theory vs. relational logic with a solver.                                                                              |
