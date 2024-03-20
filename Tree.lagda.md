```
module Tree where

open import Data.Nat
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
```

# Trees

To model file systems, I think it will be better to start directly with trees.

The nodes of the tree is uniquely indexed by integers.

```
data Tree : Set where
    leaf : ℕ → Tree
    node : ℕ → List Tree → Tree
```

The function `eq?` compares two integers.

```
eq? : ℕ → ℕ → Bool
eq? zero zero = true
eq? zero (suc _) = false
eq? (suc _) zero = false
eq? (suc m) (suc n) = eq? m n
```

`in?` checks whether an integer is already present in a tree.

```
in? : ℕ → Tree → Bool
in-children? : ℕ → List Tree → Bool

in? m (leaf n) = eq? m n
in? m (node n ns) = eq? m n ∨ in-children? n ns

in-children? m [] = false
in-children? m (n ∷ ns) = in? m n ∨ in-children? m ns
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


children-unique 
  : ∀ n ns → children-uniquely-indexed ns 
  → {!   !}
 → is-uniquely-indexed (node n ns)

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