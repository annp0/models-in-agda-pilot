```
{-# OPTIONS --guardedness #-}

module Tree where

open import Data.Nat
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product

open import Interface

open Interface.Interface
```

# Trees

To model file systems, I think it will be better to start directly with trees.

The nodes of the tree is uniquely indexed by integers.

```
data Tree : Set where
    leaf : ℕ → Tree
    node : ℕ → List Tree → Tree
```

`intree?` checks whether an integer is already present in a tree.

```
intree? : ℕ → Tree → Bool
intree-children? : ℕ → List Tree → Bool

intree? m (leaf n) = eq? m n
intree? m (node n ns) = eq? m n ∨ intree-children? n ns

intree-children? m [] = false
intree-children? m (n ∷ ns) = intree? m n ∨ intree-children? m ns

intree-help : Tree → Tree → Bool
intree-help (leaf m) t = intree? m t
intree-help (node m _) t = intree? m t
```

-- need to add comments

-- current issues: 
1. agda cannot see some impossible cases
2. need a better type for `remtree-help`, it shouldn't be the same as the parent function 

```
data TreeQs : Set where
    addQ : Tree → ℕ → TreeQs
    remQ : ℕ → TreeQs
    read : TreeQs
    movQ : ℕ → ℕ → TreeQs

TreeI : Interface
TreeI .Question = TreeQs
TreeI .Answer (addQ _ _) = Status 
TreeI .Answer (remQ _) = Status
TreeI .Answer (movQ _ _) = Status
TreeI .Answer (read) = Tree

addtree : Tree → ℕ → Tree → Status × Tree
addtree-help : Tree → ℕ → Tree → Status × Tree
addtree-children : Tree → ℕ → List Tree → Status × Tree

addtree nt n t with intree-help nt t
...                     | true = (failure , t)
...                     | false with intree? n t
...                                | false = (failure , t)
...                                | true = addtree-help nt n t

addtree-help nt m (node n ns) with eq? m n
...                              | false = addtree-children nt m ns
...                              | true = (success , node n (nt ∷ ns))
addtree-help nt m (leaf n) = (failure , leaf n)

addtree-children nt m (n ∷ ns) with (addtree-help nt m n)
...                               | (success , t) = (success , t)
...                               | (failure , _) = (addtree-children nt m ns)

addtree-children nt m [] = (failure , nt)

remtree : ℕ → Tree → Status × Tree
remtree-children : ℕ → List Tree → Status × Tree

remtree n t with intree? n t
...            | false = (failure , t)
...            | true = (success , )
remtree-help : ℕ → Tree → Status × Tree 
```

-- Todo: implement with interfaces

The following showcases an approach with evidences (very primitive)

```
data _∈ᵗ_ (n : ℕ) : Tree → Set
data _∈ᶜ_ (n : ℕ) : List Tree → Set

data _∈ᶜ_ n where
    here : ∀ {t ts} → n ∈ᵗ t → n ∈ᶜ (t ∷ ts) 
    there : ∀ {t ts} → n ∈ᶜ ts → n ∈ᶜ (t ∷ ts) 

data _∈ᵗ_ n where
    leaf : n ∈ᵗ leaf n
    node : ∀ {ns} → n ∈ᵗ node n ns
    children : ∀ {m ns} → n ∈ᶜ ns → n ∈ᵗ node m ns

is-uniquely-indexed : Tree → Set
is-uniquely-indexed t = ∀ {n} → (i j : n ∈ᵗ t) → i ≡ j

children-uniquely-indexed : List Tree → Set
children-uniquely-indexed ts = ∀ {t} → (i j : t ∈ᶜ ts) → i ≡ j

tree : Tree
tree = node 1 (leaf 2 ∷ leaf 3 ∷ [])

tree-unique : is-uniquely-indexed tree
tree-unique node node = refl
tree-unique node (children (there (here ())))
tree-unique node (children (there (there ())))
tree-unique (children (there (here ()))) node
tree-unique (children (there (there ()))) node
tree-unique (children (here leaf)) (children (here leaf)) = refl
tree-unique (children (here leaf)) (children (there (here ())))
tree-unique (children (here leaf)) (children (there (there ())))
tree-unique (children (there (here leaf))) (children (there (here leaf))) = refl

leaf-unique : ∀ n → is-uniquely-indexed (leaf n)
leaf-unique n leaf leaf = refl

```


```plain
[]-unique : children-uniquely-indexed [] 
[]-unique ()

unique? : ∀ t → Dec (is-uniquely-indexed t)
unique-children? : ∀ ts → Dec (children-uniquely-indexed ts)


unique? (leaf n) = yes (leaf-unique n)
unique? (node n ns) with unique-children? ns
... | yes p = {!   !}
... | no p = {!   !}

unique-children? [] = yes []-unique
unique-children? (x ∷ ns) = {!   !}
```