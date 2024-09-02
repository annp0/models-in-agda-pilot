## Model Description

A file system is a structured method for organizing, storing, and managing files on storage devices such as hard drives, SSDs, and USB drives.

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

From the above descriptions, we infer:

- A file system comprises two types of objects: files and directories.
- The hierarchical nature implies a tree structure with the following properties:
    - A unique root exists, which is not a member of any directory.
    - If object A is a member of directory B, then B is the parent of A.
    - Any non-root object should have a queryable parent.
    - Directory objects should allow queries for their child objects.
- Files and directories can be added to or removed from the file system. These operations must satisfy the following properties:
    - Operations only affect the targeted objects.
    - Adding an object will indeed add an object; removing an object will indeed remove an object.

Our model is expected to satisfy these specifications and properties.

### Features and Characteristics

According to [1](https://inria.hal.science/inria-00538459/document), a good model should have the following features:

- **Mapping Feature**: The model is based on common understandings of file systems as described by Wikipedia and other sources.
- **Reduction Feature**: We have abstracted away certain elements from the original description:
    - **Pathnames**: Existing file systems usually seperate the notion of files / directories themselves and their pathnames. We find this to be unnecessary: pathnames are used as unique indentifiers, but when we talk about different objects in a modelling language, we are already indentifying them in some way.
    - **Metadata**: We can just include them as the information contained in files / directories.
    - **Storage Allocation**: This aspect is ignored since the physical storage details are not the focus of our model.
- **Pragmatic Feature**: The model retains the essential features of a file system.

### Characteristics

- **Abstraction**: Non-essential details are omitted, and the core aspects of a file system are preserved.
- **Understandability/Accuracy**: The model remains both comprehensible and accurate after abstraction.
- **Predictiveness**: The model specifies key properties that are crucial for a predictable file system.
- **Inexpensiveness**: Implementing this model in a modeling language is significantly simpler than developing a real file system since detailed aspects like metadata and storage allocation are not considered.

## Our Agda Model

In our Agda model, a file system is represented as a record containing the following components:

- **`FSObj`**: The type representing file system objects.
- **`root`**: The root object among the file system objects.
- **`Info`**: The type of information associated with files.
- **`≡ᵒ`**: An equality relation between objects; we need this mainly because when querying an object's parents, we need to express that object is not root (this equality is usually established by comparing pathnames).
- **`IsDir`**: A predicate identifying directory objects.
- **`≤ᵒ`**: A preorder relation expressing containment.
- **`IsChild`**: A relation indicating membership within a directory.
- **`get-children`**: A function that retrieves all children of a given directory, along with proof of their child status.
- **`get-parent`**: A function that retrieves the parent of an object, provided the object is not the root, along with proof of its child status.
- **`remObj`**: A function that removes an object and returns the updated file system.
- **`rem-map`**: A proof that for objects unaffected by removal, there is a mapping to the new file system where their information remains unchanged.
- **`addFS` and `add-map`**: Functions similar to `remObj` and `rem-map`, but for adding objects.

This model is clearly a type theory model. As noted in [2](https://www.cse.chalmers.se/~patrikj/papers/TypeTheory4ModProg_preprint_2018-05-19.pdf), type theory models satisfy typical modeling needs, and our model confirms this:

- **Expressiveness**: Agda effectively models the structure of file systems.
- **Properties**: Properties like `IsChild` and `add-map` can be expressed as dependent-type-valued functions, which also serve as proofs. This is advantageous for reasoning since we don’t need to extract proofs from properties as with traditional boolean-valued predicates.
- **Analysis**: The type-checking process is automatic. Once the code type checks, we can say that all the results we have proven in this model is mathematically sound.

However, we identified several limitations:

- **Visualization**: There is no straightforward way to visualize a type theory model.
- **Automated Reasoning**: Proofs for every property must be manually provided, which is time-consuming and challenging. Automated reasoning would be beneficial, but Agda does not support even proving basic results automatically.

## Comparison with Alloy
We now compare our model with the alloy file system model presented at [3](https://alloytools.org/tutorials/online/frame-FS-1.html). The alloy model models file systems as follows:

- We first define `file`, `directory` as signatures, and they are both file system objects;

- We then define file system:
    - it contains a set of file system objects (`live`)
    - there is a root that is a directory, and is `live`
    - `parent` is a relation that connects anything that is not root to some directory that is live
    - `contents` connects a directory with multiple file system objects
    - live objects are reachable from root (by keep taking `contents`)
    - `parent` is the inverse of `contents`

- And we check for the following properties:
    - If we `remove` an object, then we remove the parent relation from that file to its parent
    - The same goes for `move`

It is different from our model in the following ways:

- Implementation of "objects":
	- Agda: "objects" are represented by data types. The distinction between files and directories is given by a predicate.
	- Alloy: "objects" are represented by "signatures"
- To express equality:
	- Agda: We first define equality explicitly (since this equality is different from definitional equality).
	- Alloy: Equality is established naturally, since objects are just atoms.
- To express conditions on the domain:
	- Agda: We write `(a : A) -> P a -> ...` to express this function is only defined over `(a : A)` with property `P a`.
	- Alloy: We just write `(A - B) -> ...` to express this function is not defined on the intersection of A and B
- Implementation of operations:
	- Agda: Operations are defined as functions.
	- Alloy: Operations are defined as predicates and they serve as restrictions to the SAT solver.
- Implementation of properties:
	- Agda: Properties are usually expressed in dependent types. 
	- Alloy: Properties are expressed in terms of restrictions over relations and boolean-valued predicates.
- To show there exists a model that satisfies our specifications:
	- Agda: We show the type `ISFS` is inhabited. We designed a tree model to support this interface. The process from having an interface to showing there exists such a model is nontrivial, and after this process we are sure that our specification can be satisfied for any scope. However, there are no quick ways to check if our specifications contradict themselves.
	- Alloy: We just run the SAT solver given a finite range. This allows us to quickly check the satisfiability for basic cases and generate counter examples for us to fix our specification if something was wrong. However, this method does not guarantee the absence of counterexamples in all scopes.

## Reasons

- Expressing models is relatively easy in Alloy because models are built on relations between atoms. It is very easy to restrict the domain and relations with set-theory language.

- In Agda things are less straightforward because we usually describe file systems with set-theoric language, and agda is based on type theory. Translating the notion of objects, parent, etc. to data types requires nontivial thinking.

Finally, the choice between Agda and Alloy depends on the specific needs of the modeling task -- whether one prioritizes expressive power and formal proofs (Agda) or ease of use and quick counterexample generation (Alloy).