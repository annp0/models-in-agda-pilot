## Abstract Model

A file system is a structured method for organizing, storing, and managing files on storage devices such as hard drives, SSDs, and USB drives. [1](https://en.wikipedia.org/wiki/File_system)

### Key Components of a File System

- **Files**: The fundamental unit of storage, representing a collection of data.
- **Directories**: Organizational units that group files, forming a hierarchical structure.
- **Pathnames**: Strings that specify the location of a file or directory within the file system hierarchy.
- **Metadata**: Information associated with each file, including its name, size, type, location on the storage device, timestamps (creation, modification, access times), and permissions.
- **Storage Allocation**: The method by which data is physically stored on the storage device.

### Supported Operations

- **Data Retrieval**: The file system must be capable of retrieving data from a file.
- **Directory Management**:
    - A file system can be nested within the directory structure of another file system. For example:
        - Copying data from a memory stick to a file system on a laptop.
        - Copying data within the same file system to a different location.

## The Model

From the above descriptions, in short, we want our model to have three things:

- 1. Basic Structure (Objects, Directories, Containment)
- 2. Operations (Adding, Moving, Deleting Objects)
- 3. Guarantees (Ensuring correctness of operations)

We can naturally expand those requirements to those:

- 1. A file system comprises two types of objects: files and directories. There is only a finite number of objects in a file system.
- 2. By the specifications, for each file, we should be able to know its parent; for each directory, we should be able to know its parent and children. This implies:
    - 2a. A unique root exists and is not a member of any directory, since otherwise keep taking parent function on a object can be non-converging, which implies either there is infinitely many objects or there is a loop. Both cases contradicts our specification. Since it is unique, being root or non-root has to be a decidable property.
    - 2b. If object A is a member of directory B, then B is the parent of A.
    - 2c. There is always a parent for any non-root object.
    - 2d. For every directory, we can always query its children. 
- 3. Files and directories can be added to or removed from the file system. These operations must satisfy the following properties:
    - 3a. Operations only affect the targeted objects.
    - 3b. They have localized side effects.
- 4. There is a function that takes an object and extracts its information, which could include their contents and metadata.

Our model is expected to satisfy these specifications and properties.

### Features and Characteristics

[2](https://inria.hal.science/inria-00538459/document) has identified the following features & characteristics that a good model should follow:

Features:
- **Mapping Feature**: A model is based on an original.
- **Reduction Feature**: A model only refecls a relevant selection of an original's properties.
- **Pragmatic Feature**: A model needs to be usable in place of an original with respect to some purpose.

Characteristics:
- **Abstraction**: A model is always a reduced rendering of the system that it
represents.
- **Understandability**: A model must remain in a form that directly appeals to our intuition.
- **Accuracy**: A model must provide a true-to-life representation of the modeled system's features of interest.
- **Predictiveness**: A model must correctly predict the interesting but non-onbious properties of the modeled system.
- **Inexpensiveness**: A model must be significantly cheaper to construct and
analyse than the modeled system.

We check our model against those points. As for features:

- **Mapping Feature**: The model is based on common understandings of file systems as described by Wikipedia and other sources, which is our original. 
- **Reduction Feature**: We have abstracted away certain elements from the original description:
    - **Pathnames**: Existing file systems usually seperate the notion of files / directories themselves and their pathnames. We find this to be unnecessary: pathnames are used as unique indentifiers, but when we talk about different objects in a modeling language, we are already indentifying them in some way. Therefore we didn't explicitly define path names in our model.
    - **Metadata**: We can just include them as the information contained in files / directories.
    - **Storage Allocation etc.**: This aspect is ignored since the physical storage details are not the focus of our model.
- **Pragmatic Feature**: The model retains the essential features of a file system: the APIs of our model have given ways to extract the information in files, provide all access to the file system structure, and to modify the system by adding / removing objects. This can be use in place of the original.

As for characteristics:

- **Abstraction**: By the reduction feature and pragmatic feature, we can conclude that our model has abstracted away certain elements from the original description while preserving its essential features.
- **Understandability**: The model appeals to our intuition by using the tree hierarchey. We excluded the approach of modeling file systems as graphs and so on because they are less intuitive.
- **Accuracy**: Compared to real world file systems (e.g., NTFS, ext4), the model is accurate from the following perspectives:
    - Each non-root object has a single parent, and directories can have multiple children.
    - The root is unique, and it is decidable.
    - Every file or directory, except the root, must be contained within a directory, and directories can hold multiple items.
- **Predictiveness**: The model specifies properties that are crucial for a predictable file system, for example:
    - Parent-Child consistency.
    - Operations only have localized and predictable effects: the model ensures that operations such as adding or removing files or directories only affect the targeted objects and their immediate relationships.
- **Inexpensiveness**: Implementing this model in a modeling language is significantly simpler than developing a real file system since detailed aspects like metadata and storage allocation are not considered.

## Our Agda Model

In this section, we walk through the process that leads to the concrete model we have in agda.

### Basic setup

First of all, a file system is a record that contains APIs:

```agda
record IsFS (A : Set) : Set₁ where
```

we say type `A` is a file system if we can form `IsFs A`. 

It is clear that we need to define objects, root and information. Our approach first defines the type of objects and information:

```agda
FSObj : A → Set
Info: Set
```

since root is just an object:

```agda
root : ∀ {a : A} → FSObj a
```

According to the model, `root` should be decidable. However, to say whether an object **is** root or not requires the notion of equality, which needs to be decidable as well.

```agda
_≡ᵒ_ : ∀ {a} → FSObj a → FSObj a → Set
-- it is an equivalence relation 
≡ᵒ-prop : ∀ {a} → IsEquivalence (_≡ᵒ_ {a})
-- it is decidable
_≡ᵒ?_ : ∀ {a} (obj₁ obj₂ : FSObj a) → Dec (obj₁ ≡ᵒ obj₂) 
```

with that we can say `root` is decidable:

```agda
-- define 'an object is not root'
IsNotRoot : ∀ {a} → FSObj a → Set
IsNotRoot obj = ¬ (obj ≡ᵒ root)
-- this property is decidable
IsNotRoot? : ∀ {a} (obj : FSObj a) → Dec (IsNotRoot obj)
IsNotRoot? obj = ¬? (obj ≡ᵒ? root)
```

At last, we can extract information from an object:

```agda
extract : ∀ {a} → FSObj a → Info
```

### Hierarchey structure

As previously stated, the tree-like hierarchey structure is the key to our model. We first define directories and files. We approach this by defining `IsDir` as a predicate, and the objects that can form that predicate are directories, otherwise they are files. This obviously requires `IsDir` to be decidable.

```agda
IsDir : ∀ {a} → FSObj a → Set
IsDir? : ∀ {a} → (obj : FSObj a) → Dec (IsDir obj)
-- also, root should be a dir
RootIsDir : ∀ (a : A) → IsDir
```

We need to define the child relation: `IsChild par kid` says `kid` is a child of `par`. Obviously `par` should be a directory, and for every directory we can query their children (with proof that they are indeed children).

```agda
IsChild : ∀ {a} → FSObj a → FSObj a → Set
IsChild-IsDir : ∀ {a} {par kid : FSObj a} → IsChild par kid → IsDir par
get-children : ∀ {a} → (obj : FSObj a) → IsDir obj 
            → List (Σ[ kid ∈ (FSObj a) ] IsChild obj kid)
```

Also, for any non-root object, we should also be able to query its parent.

```agda
get-parent : ∀ {a} → (obj : FSObj a) → IsNotRoot obj
    → Σ[ par ∈ (FSObj a) ] IsChild par obj
```

with this, we have set up the tree structure.

### Operations

Given an object of `A`, if it is not the root, then it can be removed:

```agda
remObj : ∀ {a} → (obj : FSObj a) → IsNotRoot obj → A
```

Given another tree structure, given a directory, we can also add that tree structure to our file system:

```agda
addFS : ∀ {a} → (obj : FSObj a) → IsDir obj → A → A
```

### Gurantees (Side Effects)

Now we model their effects: they should only affect the subtree rooted at the specified location. Therefore we need the notion of `subtree`, or more precisely `containment`. We say `o1` is contained in `o2` if we can reach `o1` starting from `o2`. This relation is obviously a preorder.

```agda
_≤ᵒ_ : ∀ {a} → FSObj a → FSObj a → Set
≤ᵒ-prop : ∀ {a} → IsPreorder (_≡ᵒ_ {a}) (_≤ᵒ_ {a}) 
```

we also define their negation for convenience:

```agda
_≰ᵒ_ : ∀ {a} → FSObj a → FSObj a → Set
_≰ᵒ_ obj₁ obj₂ = ¬ (obj₁ ≤ᵒ obj₂)
```

The effect can then be stated as follows, i.e. if the object is not contained in the location subject to the operation, this function maps the object to an object in the new file system that contains the same information.

```agda
rem-map : ∀ {a} → (objr : FSObj a) → (nr : IsNotRoot objr) → (objo : FSObj a)
    → objr ≰ᵒ objo
    → Σ[ objn ∈ FSObj (remObj objr nr) ] extract objo ≡ extract objn
add-map : ∀ {a} → (objm : FSObj a) → (idom : IsDir objm) 
    → (objo : FSObj a) → objo ≰ᵒ objm → (b : A)
    → Σ[ objn ∈ FSObj (addFS objm idom b) ] extract objo ≡ extract objn
```

### Conclusion

This model is clearly a type theory model. As noted in [2](https://www.cse.chalmers.se/~patrikj/papers/TypeTheory4ModProg_preprint_2018-05-19.pdf), type theory models satisfy typical modeling needs, and our model confirms this:

- **Expressiveness**: Agda effectively models the structure of file systems.
- **Properties**: Properties like `IsChild` and `add-map` can be expressed as dependent-type-valued functions, which also serve as proofs. This is advantageous for reasoning since we don’t need to extract proofs from properties as with traditional boolean-valued predicates.
- **Analysis**: The type-checking process is automatic. Once the code type checks, we can say that all the results we have proven in this model is mathematically sound.

However, we identified several limitations:

- **Visualization**: There is no straightforward way to visualize a type theory model.
- **Automated Reasoning**: Proofs for every property must be manually provided, which is time-consuming and challenging. Automated reasoning would be beneficial, but Agda does not support even proving basic results automatically.

## The Alloy Model

We introduce the alloy file system model presented at [3](https://alloytools.org/tutorials/online/frame-FS-1.html).

### Basic Setup

```alloy
abstract sig FSObject { }
sig File, Dir extends FSObject { }
```
- `FSObject`: Represents an **abstract** entity (either a file or directory).  
- `File`, `Dir`: Extend `FSObject` into concrete types.  

```alloy
sig FileSystem {
  live: set FSObject,
  root: Dir & live,
  parent: (live - root) ->one (Dir & live),
  contents: Dir -> FSObject
}
```
- `live`: Tracks all existing objects.  
- `root`: The single root directory.  
- `parent`: Establishes a parent-child hierarchy.  
- `contents`: Defines directory containment.  

### Operations 

- Adding Objects:

```alloy
pred add [fs, fs': FileSystem, newObj: FSObject, targetDir: Dir] {
  targetDir in fs.live
  newObj not in fs.live
  
  // Preserve existing structure except for the modification
  fs'.live = fs.live + newObj
  fs'.parent = fs.parent + newObj->targetDir
  fs'.contents = fs.contents ++ targetDir->newObj
}
```
- Objects be added if they were not in the FS.  
- The parent relationship is updated accordingly.  

- Deleting Objects:

```alloy
pred remove [fs, fs': FileSystem, x: FSObject] {
  x in (fs.live - fs.root)
  fs'.parent = fs.parent - x->(x.(fs.parent))
}
```
- Objects (except root) can be deleted.  
- The parent relationship is removed.  

### Guarantees (Correctness)

```alloy
removeOkay: check {
  all fs, fs': FileSystem, x: FSObject |
    remove[fs, fs', x] => fs'.live = fs.live - x
} for 5
```
- Checks that Deleting removes exactly one object.  It's similar for add.

## Comparison between the Alloy Model and our Agda model

### Basic Structure

The abstract model defines a file system as a collection of objects organized in a hierarchy.  

#### Agda Model

Agda captures this hierarchy using a record type (`IsFS`), which formalizes: 

- Objects (`FSObj`)  
- Root Directory (`root`)  
- Containment Relations (`≤ᵒ`)  

```agda
record IsFS (A : Set) : Set₁ where
    field
        FSObj : A → Set  -- Defines objects in the FS
        root : ∀ {a} → FSObj a  -- Unique root directory
        _≤ᵒ_ : ∀ {a} → FSObj a → FSObj a → Set  -- Containment relation
```
- `FSObj` corresponds to the abstract notion of a file system object.  
- `root` enforces the requirement that there is a unique entry point.  
- `_≤ᵒ_` ensures a well-defined hierarchy, where objects are contained within directories.  

#### Alloy Model

Alloy defines similar concepts using signatures and relations:

```alloy
abstract sig FSObject { }
sig File, Dir extends FSObject { }
```
- `FSObject` corresponds to `FSObj` in Agda.  
- `File` and `Dir` extend `FSObject`, just as Agda could define `IsFile` and `IsDir`.  

The root directory is explicitly declared:  

```alloy
sig FileSystem {
  root: Dir & live
}
```
This matches `root` in Agda.  

### Operations

The abstract model defines operations that modify the file system:  
- Adding an object  
- Removing an object

#### Adding Objects

In Agda, it is implemented as a field for a function:

```
addFS : ∀ {a} → (obj : FSObj a) → IsDir obj → A → A
```

The constraints are given as a term of certain type, and we do not need to implement this function immediately - however, to show such model exists, we eventually need to supply an example of `A` and `addFS`. 

In Alloy it is as follows:

```
pred add [fs, fs': FileSystem, newObj: FSObject, targetDir: Dir] {
  targetDir in fs.live
  newObj not in fs.live
  
  // Preserve existing structure except for the modification
  fs'.live = fs.live + newObj
  fs'.parent = fs.parent + newObj->targetDir
  fs'.contents = fs.contents ++ targetDir->newObj
}
```

This directly manipulates the set of relations.

For deletion operations, it is similar.

### Guarantees  

The abstract model ensures that operations preserves structure (i.e. only have local side effects).

In Agda, this is done by another field that asks for a function that will return a term of the desired type.

```agda
add-map : ∀ {a} → (objm : FSObj a) → (idom : IsDir objm) 
    → (objo : FSObj a) → objo ≰ᵒ objm → (b : A)
    → Σ[ objn ∈ FSObj (addFS objm idom b) ] extract objo ≡ extract objn
```

In Alloy, since the constraints are already in the definition, we can directly run the predicate to check behavior:

```
run addFS for 2 FileSystem, 5 FSObject
```

### Conclusion of Comparison

From the modeling standpoint:

| Feature | Abstract Model | Agda Model | Alloy Model |
|---------|---------------|------------|-------------|
| Objects | Files, Directories | `FSObj` data type | `sig FSObject` |
| Parent-Child Relationship | Defined explicitly | `IsChild` predicate | `contents` and `parent` relations |
| Root | Unique, no parent | `root : FSObj a` | `root: Dir & live` |
| Operations | Add, Remove | `addFS`, `remObj` | `add`, `remove` |
| Hierarchy Enforcement | Explicitly stated | `IsDir`, `IsChild` | `parent = ~contents` |
| Localized Effects | Enforced | `rem-map`, `add-map` | `fs'.live = fs.live - x`, etc. |
| Verification | Manual proof | Dependent types ensure correctness | SAT solver generates counterexamples |

In terms of language features:

| **Aspect**                               | **Agda**                                                            | **Alloy**                                                   |
|------------------------------------------|---------------------------------------------------------------------|-------------------------------------------------------------|
| **Implementation of "objects"**          | "Objects" are represented by data types. The distinction between files and directories is given by a predicate. | "Objects" are represented by "signatures".                |
| **To express equality**                  | We first define equality explicitly (since this equality is different from definitional equality). | Equality is established naturally, since objects are just atoms. |
| **To express conditions on the domain**  | We write `(a : A) -> P a -> ...` to express this function is only defined over `(a : A)` with property `P a`. | We just write `(A - B) -> ...` to express this function is not defined on the intersection of A and B. |
| **Implementation of operations**         | Operations are defined as functions.                                | Operations are defined as predicates and they serve as restrictions to the SAT solver. |
| **Implementation of properties**         | Properties are usually expressed in dependent types.                 | Properties are expressed in terms of restrictions over relations and boolean-valued predicates. |
| **To show there exists a model that satisfies our specifications** | We show the type `ISFS` is inhabited. We designed a tree model to support this interface. The process from having an interface to showing there exists such a model is nontrivial, and after this process we are sure that our specification can be satisfied for any scope. However, there are no quick ways to check if our specifications contradict themselves. | We just run the SAT solver given a finite range. This allows us to quickly check the satisfiability for basic cases and generate counterexamples for us to fix our specification if something was wrong. However, this method does not guarantee the absence of counterexamples in all scopes. |

### Analysis of Key Design Choices

Both models made important design choices that weren't strictly forced by the requirements:

#### The 'live' Concept in Alloy

The Alloy model introduces a 'live' set that tracks existing objects, which isn't explicitly mentioned in the requirements or implemented in the Agda model:

```alloy
sig FileSystem {
  live: set FSObject,
  ...
}
```

This design choice stems from Alloy's relational approach:

1. Alloy needs an explicit mechanism to differentiate between potential objects in the universe and those currently existing in the file system
2. The 'live' set provides a natural boundary for operations - `add` brings objects into this set, and `remove` takes them out
3. 'live' also serves as a state-tracking mechanism

The Agda model achieves the same goal differently through its parameterization of file systems by the collection of objects (`FSObj : A → Set`). When operations like `addFS` or `remObj` create new file system states, objects are intrinsically tied to specific file systems, eliminating the need for explicit "liveness" tracking.

#### Data Types vs. Signatures

The choice of using parameterized data types in Agda versus signatures in Alloy reflects their different foundations:

Agda:
- Modeling objects as a family of types indexed by file system state (`FSObj : A → Set`) is a natural choice from Agda's functional programming design
- This naturally establishes signatures as claims and implementations as proofs by the Curry-Howard correspondence.
- Using predicates rather than "classes" allows more flexible reasoning about object properties

Alloy:
- Alloy's relational logic makes signatures (representing sets of atoms) the natural modeling primitive
- The inheritance relationship `sig File, Dir extends FSObject` directly mirrors the conceptual "is-a" relationship
- This also allows Alloy's analyzer to directly visualize these atom-based objects and their relationships

### Summary

- Expressing models is relatively easy in Alloy because models are built on relations between atoms. It is very easy to restrict the domain and relations with set-theory language.

- In Agda things are less straightforward because we usually describe file systems with set-theoric language, and agda is based on type theory. Translating the notion of objects, parent, etc. to data types requires nontivial thinking.