```agda
{-# OPTIONS --guardedness #-}

module Tree where

open import Data.List
open import Data.Maybe
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

For specification 2: (the `add` operation)

```agda
-- filterⁱ removes a member of a list, given the proof of membership
filterⁱ : ∀ {xs : List Tree} {x : Tree} → (x ∈ xs) → List Tree
filterⁱ {x ∷ xs} {y} here = xs
filterⁱ {x ∷ xs} {y} (there y∈xs) = x ∷ (filterⁱ {xs} {y} y∈xs) 

-- addᵗ adds a tree to a node (specified by a path)
addᵗ : ∀ {x y : Tree} → (x ⇒ y) → isnode y → Tree → Tree
addᵗ {x} {y} self (fromnode {xs}) z = node (z ∷ xs)
addᵗ {node xs} {y} (child (inᶜ y∈xs)) isnode-y z = 
    node ((addᵗ (self {y}) isnode-y z) ∷ (filterⁱ y∈xs))
addᵗ {node xs} {z} (trans {y} (inᶜ y∈xs) y⇒z) isnode-z a = 
    node ((addᵗ y⇒z isnode-z a) ∷ filterⁱ y∈xs)

-- the added element now has a path
addᵗ-⇒ : ∀ {x y z : Tree} → (x⇒y : x ⇒ y) → (isnode-y : isnode y) → 
        (addᵗ x⇒y isnode-y z) ⇒ z
addᵗ-⇒ {x} {x} {z} (self) (fromnode {xs}) = child (inᶜ (here {z} {xs}))
addᵗ-⇒ {node xs} {y} {z} (child (inᶜ y∈xs)) isnode-y = 
        trans (inᶜ here) (addᵗ-⇒ self isnode-y)
addᵗ-⇒ {node xs} {z} {a} (trans {y} (inᶜ y∈xs) y⇒z) (isnode-z) = 
        trans (inᶜ here) (addᵗ-⇒ y⇒z isnode-z)
```

For specification 3: (the `remove` operation)

```agda
remᵗ : ∀ {x y : Tree} → x ⇒ y → Maybe Tree
-- if we remove the root, we get nothing
remᵗ self = nothing
remᵗ {node xs} {y} (child (inᶜ y∈xs)) = just (node (filterⁱ y∈xs))
remᵗ {node xs} {z} (trans {y} (inᶜ y∈xs) y⇒z) 
    with remᵗ y⇒z
...    | nothing = just (node (filterⁱ y∈xs))
...    | just y′ = just (node (y′ ∷ filterⁱ y∈xs))
```