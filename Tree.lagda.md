```agda
{-# OPTIONS --guardedness #-}

module Tree where

open import Data.Empty
open import Data.Unit using (⊤)
open import Data.List
open import Data.Maybe
open import Data.Nat.Base
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong)
open import Relation.Nullary using (¬_)
```


# Trees

To model file systems, I think it will be better to start directly with trees.

Specifications:

1. Each node has a list (set) of children
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

-- If we know that a tree has a child, then it
-- must be a node.
unnode : ∀ {x} → (y : Tree) → x ∈ᶜ y → List Tree
unnode (node ys) p = ys

-- Turn a tree membership proof into a list membership proof.
outᶜ : ∀ {x y} → (x∈y : x ∈ᶜ y) → x ∈ unnode y x∈y
outᶜ (inᶜ x∈y) = x∈y

-- x ⇒ y records the path from x to y
data _⇒_ : Tree → Tree → Set where
    self : ∀ {t : Tree} → t ⇒ t
    trans : ∀ {y x z : Tree} → y ∈ᶜ x → y ⇒ z → x ⇒ z

-- ♭ x can only be formed when x is a node
data ♭_ : Tree → Set where
    node : ∀ {xs : List Tree} → ♭ (node xs)
```

For specification 2: (the `add` operation)

```agda
-- filterⁱ removes a member of a list, given the proof of membership
filterⁱ : ∀ {xs : List Tree} {x : Tree} → (x ∈ xs) → List Tree
filterⁱ {x ∷ xs} {y} here = xs
filterⁱ {x ∷ xs} {y} (there y∈xs) = x ∷ (filterⁱ {xs} {y} y∈xs) 

-- For two same elements in a list, after removing one element
-- the other element is still present in the list
filter-sameⁱ : ∀ {x xs} → (p q : x ∈ xs) → p ≢ q → x ∈ filterⁱ p 
filter-sameⁱ here here p≠q = ⊥-elim (p≠q refl)
filter-sameⁱ here (there q) p≠q = q
filter-sameⁱ (there p) here p≠q = here
filter-sameⁱ (there p) (there q) p≠q = there (filter-sameⁱ p q (p≠q ∘ cong there))

-- replace x with a new tree
setⁱ : ∀ {x} → (xs : List Tree) → x ∈ xs → Tree → List Tree
setⁱ (_ ∷ xs) here x'      = x' ∷ xs
setⁱ (x ∷ xs) (there p) x' = x ∷ setⁱ xs p x'

-- by replacing x with x we still have the original list
set-getⁱ : ∀ {x xs} → (x∈xs : x ∈ xs) → setⁱ xs x∈xs x ≡ xs
set-getⁱ here = refl
set-getⁱ (there p) = cong (_ ∷_) (set-getⁱ p) 

-- by replacing x with x' we will have the proff that 
-- x' is in the new list
get-setⁱ : ∀ {x x' xs} → (x∈xs : x ∈ xs) → x' ∈ setⁱ xs x∈xs x'
get-setⁱ here = here
get-setⁱ (there p) = there (get-setⁱ p)

-- if y is not x, and we replace x with x', then y is still in
-- the original list
set-otherⁱ : ∀ {x x' y xs} → (x∈xs : x ∈ xs) (y∈xs : y ∈ xs) → x ≢ y → y ∈ setⁱ xs x∈xs x'
set-otherⁱ here here x≠y = ⊥-elim (x≠y refl)
set-otherⁱ here (there y∈xs) x≠y = there y∈xs
set-otherⁱ (there x∈xs) here x≠y = here
set-otherⁱ (there x∈xs) (there y∈xs) x≠y = there (set-otherⁱ x∈xs y∈xs x≠y)

-- if there are two `x`s in the list `xs`, and we replace one
-- of the `x`s with `x'`, then x is still in `xs` 
set-sameⁱ : ∀ {x x' xs} → (x∈xs x∈xs' : x ∈ xs) → x∈xs ≢ x∈xs' → x ∈ setⁱ xs x∈xs x'
set-sameⁱ here here not-eq = ⊥-elim (not-eq refl)
set-sameⁱ here (there x∈xs') not-eq = there x∈xs'
set-sameⁱ (there x∈xs) here not-eq = here
set-sameⁱ (there x∈xs) (there x∈xs') not-eq = there (set-sameⁱ x∈xs x∈xs' (not-eq ∘ cong there))

-- addᵗ adds a tree to a node (specified by a path)
addᵗ : ∀ {x y : Tree} → (x ⇒ y) → ♭ y → Tree → Tree
addᵗ {x} {y} self (node {xs}) z = node (z ∷ xs)
-- addᵗ {node xs} {y} (child (inᶜ y∈xs)) ♭y z = 
--     node ((addᵗ (self {y}) ♭y z) ∷ (filterⁱ y∈xs))
addᵗ {node xs} {z} (trans {y} (inᶜ y∈xs) y⇒z) ♭z a = 
    node ((addᵗ y⇒z ♭z a) ∷ filterⁱ y∈xs)

-- the added element now has a path
addᵗ-⇒ : ∀ {x y z : Tree} → (x⇒y : x ⇒ y) → (♭y : ♭ y) → 
        (addᵗ x⇒y ♭y z) ⇒ z
addᵗ-⇒ {x} {x} {z} (self) (node {xs}) =  {!   !}
    -- child (inᶜ (here {z} {xs}))
addᵗ-⇒ {node xs} {z} {a} (trans {y} (inᶜ y∈xs) y⇒z) ♭z = 
        trans (inᶜ here) (addᵗ-⇒ y⇒z ♭z)
```

For specification 3: (the `remove` operation)

```agda
-- remᵗ : ∀ {x y : Tree} → x ⇒ y → Maybe Tree
-- -- if we remove the root, we get nothing
-- remᵗ self = nothing
-- remᵗ {node xs} {z} (trans {y} (inᶜ y∈xs) y⇒z) 
--     with remᵗ y⇒z
-- ...    | nothing = just (node (filterⁱ y∈xs))
-- ...    | just y′ = just (node (y′ ∷ filterⁱ y∈xs))

-- x ≺ y states that "x is a subtree of y".
-- maybe this new relation will make it easier?
data _≺_ (x y : Tree) : Set where
    child : x ∈ᶜ y → x ≺ y
    trans : ∀ {a} → x ∈ᶜ a → a ≺ y → x ≺ y

-- the closure
data _≼_ (x : Tree) : Tree → Set where
    self : x ≼ x
    smaller : ∀ {y} → x ≺ y → x ≼ y

≺-trans : ∀ {x y z} → x ≺ y → y ≺ z → x ≺ z
≺-trans (child x∈y) y≺z = trans x∈y y≺z
≺-trans (trans x∈a a≺y) y≺z = trans x∈a (≺-trans a≺y y≺z)

≼-trans : ∀ {x y z} → x ≼ y → y ≼ z → x ≼ z
≼-trans = {!   !}
```

Well founded relations 

(The following can be found in `Induction.WellFounded`, just playing around)

```agda
data Acc {A : Set} (_<_ : A → A → Set) (x : A) : Set where
    acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x

WellFounded : ∀ {A : Set} → (A → A → Set) → Set
WellFounded _<_ = ∀ x → Acc _<_ x

module _ {A : Set} {_<_ : A → A → Set} (wf : WellFounded _<_) where

  wf-irrefl : ∀ {x} → x < x → ⊥
  wf-irrefl {x} x<x = go (wf x)
    where 
      go : Acc _<_ x → ⊥
      go (acc rec) = go (rec x x<x)
```

```agda
leaf-⊀ : ∀ {x} → x ≺ leaf → ⊥
leaf-⊀ (trans _ p) = leaf-⊀ p

node-[]-⊀ : ∀ {xs} → xs ≺ node [] → ⊥
node-[]-⊀ (child (inᶜ ()))
node-[]-⊀ (trans x p) = node-[]-⊀ p

-- We should show ≺ is wellfounded?
```

Some attempts

```agda
setᵗ : ∀ {x : Tree} → (y : Tree) → (x ≺ y) → Tree → Tree
setᵗ y (child x∈y) x' = node (setⁱ (unnode y x∈y) (outᶜ x∈y) x')
setᵗ y (trans {a = node as} x∈a a≺y) x' = setᵗ y a≺y (node (setⁱ as (outᶜ x∈a) x'))

remᵗ : ∀ {x y : Tree} → (p : x ≺ y) → Tree
remᵗ (child x∈y) = node (filterⁱ (outᶜ x∈y))
remᵗ (trans x∈y y≺z) = setᵗ _ y≺z (node (filterⁱ (outᶜ x∈y)))

set-sameᵗ : ∀ {x x' y} → (p q : x ≺ y) → p ≢ q → x ≺ setᵗ y p x'
set-sameᵗ (child (inᶜ x∈y)) (child (inᶜ x∈y')) p≠q = 
      child (inᶜ (set-sameⁱ x∈y x∈y' (p≠q ∘ cong (child ∘ inᶜ))))
set-sameᵗ (child (inᶜ x∈y)) (trans x∈a q) p≠q = 
      trans x∈a {!   !}
set-sameᵗ (trans x p) q p≠q = {!   !}

rem-otherᵗ : ∀ {x x' y : Tree} → (p : x ≺ y) → ¬ (x' ≺ x) → x ≺ remᵗ p
rem-otherᵗ p = {!   !}

rem-sameᵗ : ∀ {x y : Tree} → (p q : x ≺ y) → p ≢ q → x ≺ remᵗ p
rem-sameᵗ (child (inᶜ p)) (child (inᶜ q)) p≠q = 
    child (inᶜ (filter-sameⁱ p q (p≠q ∘ cong (child ∘ inᶜ))))
rem-sameᵗ (child (inᶜ p)) (trans x∈a a≺y) p≠q = 
    {!   !}
rem-sameᵗ (trans (inᶜ x∈y) p) (child (inᶜ x∈y')) p≠q = child {!   !}
rem-sameᵗ (trans x p) (trans x₁ q) p≠q = {!   !}
```