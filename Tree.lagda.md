```
{-# OPTIONS --guardedness #-}

module Tree where

open import Data.Nat
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
```

# Trees

To model file systems, I think it will be better to start directly with trees.

The nodes of the tree is indexed by integers.

```
data Tree : Set where
    leaf : ℕ → Tree
    node : ℕ → List Tree → Tree
```

The problem is that we want them to be **uniquely** indexed by integers.

# An approach with evidences

```
-- _∈ᵗ_ is the evidence that a number is in the tree
-- _∈ᶜ_ is the evidence that a number is in a list of trees

data _∈ᵗ_ (n : ℕ) : Tree → Set
data _∈ᶜ_ (n : ℕ) : List Tree → Set

data _∈ᶜ_ n where
    here : ∀ {t ts} → n ∈ᵗ t → n ∈ᶜ (t ∷ ts) 
    there : ∀ {t ts} → n ∈ᶜ ts → n ∈ᶜ (t ∷ ts) 

data _∈ᵗ_ n where
    leaf : n ∈ᵗ leaf n
    node : ∀ {ns} → n ∈ᵗ node n ns
    children : ∀ {m ns} → n ∈ᶜ ns → n ∈ᵗ node m ns
```

Now being uniquely indexed is equivalent to the fact that
for every number in the tree, the evidence is unique.

```
is-uniquely-indexed : Tree → Set
is-uniquely-indexed t = ∀ {n} → (i j : n ∈ᵗ t) → i ≡ j
```

This is saying that a list of trees is uniquely indexed.
Might come in handy later.

```
children-uniquely-indexed : List Tree → Set
children-uniquely-indexed ts = ∀ {t} → (i j : t ∈ᶜ ts) → i ≡ j
```

Obviously a leaf and an empty list is uniquely indexed.

```
leaf-unique : ∀ n → is-uniquely-indexed (leaf n)
leaf-unique n leaf leaf = refl

[]-unique : children-uniquely-indexed [] 
[]-unique ()
```

An example showcasing a small tree and proving its unique index property.

```
tree : Tree
tree = node 1 (leaf 2 ∷ leaf 3 ∷ [])

tree-unique : is-uniquely-indexed tree
tree-unique node node = refl
tree-unique node (children (there (here ())))
tree-unique node (children (there (there ())))
tree-unique (children (there (here ()))) node
tree-unique (children (there (there ()))) node
tree-unique (children (here leaf)) (children (here leaf)) = cong children refl
tree-unique (children (here leaf)) (children (there (here ())))
tree-unique (children (here leaf)) (children (there (there ())))
tree-unique (children (there (here leaf))) (children (there (here leaf))) = cong children refl

```
The goal: a decidable algorithm

```agda
unique? : ∀ t → Dec (is-uniquely-indexed t)
unique-children? : ∀ ts → Dec (children-uniquely-indexed ts)

unique? (leaf n) = yes (leaf-unique n)
unique? (node n ns) with unique-children? ns
... | yes p = {!   !}
... | no p = {!   !}

unique-children? [] = yes []-unique
unique-children? (x ∷ ns) = {!   !}
```