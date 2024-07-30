## The specification: file systems
File systems are modeled as follows:
1. There are two kinds of "objects": files and directories. 
2. There is a unique directory called `root`.
3. If an object `A` is a child of another object (directory) `B`, then there is a relation called `ischildren`. `isparent` is defined by reversing `ischildren`. For every directory, we can query it's children, and for every object other than root, we can query its parent.

Operations on file systems are modeled as follows:
1. `add`: we can move a file system into a directory of another file system. This is useful in the following scenarios:
	1. We are copying something on a memory stick into a file system on a laptop;
	2. We are copying something within a file system to somewhere else within the same file system (this requires us to be able to repack a directory as a file system, which can be easily done in the `tree` model)
2. `remove`: we can remove an object within a file system.
3. `move`: we can move an object to a different directory within the same file system.
## Comparison
1. Implementation of "objects":
	- Agda: "objects" are represented by data types. The distinction between files and directories is given by a predicate.
	- Alloy: "objects" are represented by "signatures"
2. To express equality:
	- Agda: We first define equality explicitly (since this equality is different from definitional equality).
	- Alloy: Equality is established naturally.
3. To express conditions on the domain:
	- Agda: We write `(a : A) -> P a -> ...` to express this function is only defined over `(a : A)`s with property `P a`.
	- Alloy: We just write `(A - B) -> ...` to express this function is not defined on the intersection of `A` and `B`
4. Implementation of operations:
	- Agda: Operations are defined as functions.
	- Alloy: Operations are defined as predicates and they serve as restrictions to the SAT solver.
5. Implementation of properties:
	- Agda: Properties are usually expressed in dependent types. 
	- Alloy: Properties are expressed in terms of restrictions over relations. And to check for counterexamples, we just run the SAT solver.
6. To show there exists a model that satisfies our specifications:
	- Agda: We show the type `ISFS` is inhabited. We designed a tree model to support this interface. The process from having an interface to showing there exists such a model is nontrivial, and after this process we are sure that our specification can be satisfied for any scope. However, there are no quick ways to check if our specifications contradict themselves.
	- Alloy: We just run the SAT solver given a finite range. This allows us to quickly check the satisfiability for basic cases and generate counter examples for us to fix our specification if something was wrong. However, this method does not guarantee the absence of counterexamples in all scopes.
## Reasons
- Expressing models is relatively easy in Alloy is relatively easy because models are built on relations between atoms, where it is very easy to restrict the domain and relations with set-theory language.
- In Agda things are less straightforward because:
	- It slightly differs from the set theory language. For example, `A ⊎ B` is a completely different type and we need to use constructors `inj` to take out the elements, while in set theory it would have been much more straightforward.
	- It uses data types. This made equalities harder, since two files given by the same constructor `file` in different locations should not be equal. If we see those two files as distinct atoms within type `File` as in Alloy, this does not present a problem.
