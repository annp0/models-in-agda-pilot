```agda
open import Data.Bool
open import Data.List
open import Data.Product
```

```agda
data TreeShape : Set where
    leaf    : TreeShape
    []    : List TreeShape → TreeShape

data TreeList : List TreeShape → Set
data Tree : TreeShape → Set

data TreeList where
    []  : TreeList []
    _∷_ : (x : TreeShape) (xs : List TreeShape) 
            → Tree x → TreeList xs → TreeList (x ∷ xs)  

data Tree where
    leaf    : (x : Bool) → Tree leaf 
    node    : (x : Bool) → List Tree
```

```plaintext
-- The type of List Tree * unclear

data TreeShape : Set where
    leaf    : TreeShape
    node    : List TreeShape → TreeShape

data TreeList : List TreeShape → Set
data Tree : TreeShape → Set

data TreeList where
    []  : TreeList []
    _∷_ : (x : TreeShape) (xs : List TreeShape) 
            → Tree x → TreeList xs → TreeList (x ∷ xs)  

data Tree where
    leaf    : (x : Bool) → Tree leaf 
    node    : (x : Bool) → List Tree
```


```plaintext
-- implementation too messy
-- didn't separate paths from content

data Tree : Set
data Notin : List Tree → Set

data Tree where
    leaf : Bool → Tree
    node-in : List Tree → Tree
    node-no : ∀ {l : List Tree} → Notin l → Tree

data Notin where 
    [] : Notin []
    leaf : ∀ {l : List Tree} → Notin (leaf false ∷ l)
    node : ∀ {l ns : List Tree} {n-ns : Notin ns} → Notin (node-no n-ns ∷ l)

data NotIn : Tree → Set where
    leaf : NotIn (leaf false)
    node : ∀ {l : List Tree} {n-l : Notin l} → NotIn (node-no n-l)

data In : Tree → Set where
    leaf : In (leaf true)
    node : ∀ {l : List Tree} → In (node-in l)

data Root : Tree → Set where
    root : ∀ {ns : List Tree} → Root (node-in ns)

data _∈_ : Tree → List Tree → Set where
    here : ∀ {x : Tree} {xs : List Tree} → x ∈ (x ∷ xs)
    there : ∀ {x y : Tree} {xs : List Tree} → x ∈ xs → x ∈ (y ∷ xs)

data _∈ᶜ_ : Tree → Tree → Set where
    child-in : ∀ {t : Tree} {ts : List Tree} → (t ∈ ts) → t ∈ᶜ (node-in ts)
    child-no : ∀ {t : Tree} {ts : List Tree} {n-ts : Notin ts} → (t ∈ ts) → t ∈ᶜ (node-no n-ts) 

data _⇒_ : Tree → Tree → Set where
    child : ∀ {x y : Tree} → y ∈ᶜ x → x ⇒ y
    tran : ∀ {y x z : Tree} → y ∈ᶜ x → y ⇒ z → x ⇒ z

set : ∀ {x} → (xs : List Tree) → x ∈ xs → Tree → List Tree 
set (_ ∷ xs) here y = y ∷ xs 
set (x ∷ xs) (there p) y = x ∷ set xs p y

add : ∀ {x y : Tree} → NotIn y → (x ⇒ y) → Tree 
add {leaf _} {y} ny (child ())
add {leaf _} {y} ny (tran () x⇒y) 
add {node-in xs} {y@(leaf false)} leaf (child (child-in y∈xs)) 
    = node-in (set xs y∈xs (leaf true))
add {node-in xs} {y@(node-no {ys} n-ys)} node (child (child-in y∈xs)) 
    = node-in (set xs y∈xs (node-in ys))
add {node-in xs} {z} nz (tran {y} (child-in y∈xs) y⇒z) 
    = node-in (set xs y∈xs (add nz y⇒z))
add {node-no {xs} _} {y@(leaf false)} leaf (child (child-no y∈xs)) 
    = node-in (set xs y∈xs (leaf true))
add {node-no {xs} _} {y@(node-no {ys} n-ys)} node (child (child-no y∈xs)) 
    = node-in (set xs y∈xs (node-in ys))
add {node-no {xs} _} {z} nz (tran {y} (child-no y∈xs) y⇒z) 
    = node-in (set xs y∈xs (add nz y⇒z)) 
```