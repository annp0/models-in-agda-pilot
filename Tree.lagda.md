```agda
{-# OPTIONS --guardedness #-}

module Tree where

open import Data.List
```

# Trees

To model file systems, I think it will be better to start directly with trees.

Specifications:

1. Each node has a list of children
2. There is an `add` operation which takes in a path and a tree, 
add that tree to the node that the path points to. Will fail if the path points 
to a leaf.
3. There is a `remove` operation which takes in a path and a tree, and remove the 
leaf / node the path points to. 

For specification 1:

```agda
data Tree : Set where
    leaf : Tree
    node : List Tree → Tree

-- Membership relation (the one comes from stdlib is not easy to use)
data _∈_ : Tree → List Tree → Set where
    here : ∀ {x : Tree} {xs : List Tree} → x ∈ (x ∷ xs)
    there : ∀ {x y : Tree} {xs : List Tree} → x ∈ xs → x ∈ (y ∷ xs)

-- y ∈ᶜ x if y is a child of x
data _∈ᶜ_ : Tree → Tree → Set where
    inᶜ : ∀ {t : Tree} {ts : List Tree} 
                 → (t ∈ ts) → t ∈ᶜ (node ts)

-- x ⇒ y records the path from x to y
data _⇒_ : Tree → Tree → Set where
    self : ∀ {t : Tree} → t ⇒ t
    child : ∀ {x y : Tree} → y ∈ᶜ x → x ⇒ y
    trans : ∀ {y x z : Tree} → y ∈ᶜ x → y ⇒ z → x ⇒ z

-- isnode x can only be formed when x is a node
data isnode : Tree → Set where
    fromnode : ∀ {xs : List Tree} → isnode (node xs)
```

For specification 2: (the operation `add`)

```agda
-- filterⁱ removes a member of a list, given the proof of membership
filterⁱ : (xs : List Tree) → (x : Tree) → (x ∈ xs) → List Tree
filterⁱ (x ∷ xs) y here = xs
filterⁱ (x ∷ xs) y (there y∈xs) = x ∷ (filterⁱ xs y y∈xs) 

-- addᵗ adds a tree to a node (specified by a path)
addᵗ : ∀ {x y : Tree} → (x ⇒ y) → isnode y → Tree → Tree
addᵗ {x} {y} self (fromnode {xs}) z = node (z ∷ xs)
addᵗ {node xs} {y} (child (inᶜ y∈xs)) isnode-y z = 
    node ((addᵗ (self {y}) isnode-y z) ∷ (filterⁱ xs y y∈xs))
addᵗ {node xs} {z} (trans {y} (inᶜ y∈xs) yRz) isnode-z a = node ((addᵗ yRz isnode-z a) ∷ filterⁱ xs y y∈xs)

-- the added element now has a path
addᵗ-⇒ : ∀ {x y z : Tree} → (xRy : x ⇒ y) → (isnode-y : isnode y) → 
        (addᵗ xRy isnode-y z) ⇒ z
addᵗ-⇒ {x} {x} {z} (self) (fromnode {xs}) = child (inᶜ (here {z} {xs}))
addᵗ-⇒ {node xs} {y} {z} (child (inᶜ y∈xs)) isnode-y = 
        trans (inᶜ here) (addᵗ-⇒ self isnode-y)
addᵗ-⇒ {node xs} {z} {a} (trans {y} (inᶜ y∈xs) yRz) (isnode-z) = 
        trans (inᶜ here) (addᵗ-⇒ yRz isnode-z)
```