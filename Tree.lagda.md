```agda
{-# OPTIONS --exact-split #-}
open import Data.Bool
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import Data.Empty
```

# The Rose-tree approach, with all paths already given 

To get a content-independent path, we define the shape of a tree.

```agda
data TreeShape : Set where
    leaf    : TreeShape
    node    : List TreeShape → TreeShape
```

Trees are indexed by TreeShape, just like `Vec Nat` and Nat

Must define a new type `TreeList` for a list of trees, since
it needs to be indexed by a list of shapes now.

The contents of a tree are boolean values, representing whether
the respective nodes are in the tree (valid) or not (invalid)

```agda 
data TreeList : List TreeShape → Set
data Tree : TreeShape → Set

data TreeList where
    []      : TreeList []
    _∷_     : ∀ {x : TreeShape} {xs : List TreeShape} 
            → Tree x → TreeList xs → TreeList (x ∷ xs)  

data Tree where
    leaf    : (x : Bool) → Tree leaf
    node    : ∀ {ts : List TreeShape} 
            → Bool → TreeList ts → Tree (node ts) 
```

The paths now are purely on shapes now

```agda
data _∈_ : TreeShape → List TreeShape → Set where
    here    : ∀ {x : TreeShape} {xs : List TreeShape} → x ∈ (x ∷ xs)
    there   : ∀ {x y : TreeShape} {xs : List TreeShape} 
            → x ∈ xs → x ∈ (y ∷ xs)

data _∈ᶜ_ : TreeShape → TreeShape → Set where
    child   : ∀ {t : TreeShape} {ts : List TreeShape} 
            → (t ∈ ts) → t ∈ᶜ (node ts) 

data _⇒_ : TreeShape → TreeShape → Set where
    self    : ∀ {t : TreeShape} → t ⇒ t
    tran    : ∀ {y x z : TreeShape} → y ∈ᶜ x → y ⇒ z → x ⇒ z
```

The basic functions to traverse and change the content of the tree.
Since the collection of all valid paths is already given, the shape
cannot be modified.

```agda
get-list    : ∀ {x : TreeShape} {xs : List TreeShape} 
            → x ∈ xs → TreeList xs → Tree x 
get-list here (x ∷ x₁)          = x
get-list (there x) (x₁ ∷ x₂)    = get-list x x₂

get : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Tree y 
get self x₁                         = x₁
get (tran (child x) x₂) (node _ x₃) = get x₂ (get-list x x₃)

valid? : ∀ {x : TreeShape} → Tree x → Bool
valid? (leaf x)     = x
valid? (node x _)   = x

get-valid? : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Bool
get-valid? x x₁ = valid? (get x x₁)

valid : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Set
valid x x₁ = (get-valid? x x₁) ≡ true

invalid : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Set
invalid x x₁ = (get-valid? x x₁) ≡ false 
```

`get-set` will change the boolean value of a node, given the path to that node.
Now the `add` operation is just changing it to `true`,
the `remove` operation is just changing it to `false`.

```agda
get-set         : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Bool → Tree x
get-set-help    : ∀ {y z : TreeShape} {xs : List TreeShape} → y ∈ xs 
                → y ⇒ z → TreeList xs → Bool → TreeList xs
get-set self (leaf _) x₂                    = leaf x₂
get-set self (node _ x₁) x₂                 = node x₂ x₁
get-set (tran (child x) x₃) (node x₁ x₄) x₂ = node x₁ (get-set-help x x₃ x₄ x₂)
get-set-help here x₁ (x ∷ x₂) x₃            = get-set x₁ x x₃ ∷ x₂
get-set-help (there x) x₁ (x₂ ∷ x₄) x₃      = x₂ ∷ get-set-help x x₁ x₄ x₃

get-set-prop        : ∀ {x y : TreeShape} {x⇒y : x ⇒ y} {tx : Tree x} {b : Bool} 
                    → get-valid? x⇒y (get-set x⇒y tx b) ≡ b 
get-set-prop-help   : ∀ {y z : TreeShape} {y⇒z : y ⇒ z} {xs : List TreeShape} 
                        {txs : TreeList xs} {y∈xs : y ∈ xs} {b : Bool}
                    → valid? (get y⇒z (get-list y∈xs (get-set-help y∈xs y⇒z txs b))) 
                    ≡ b
get-set-prop {.leaf} {.leaf} {self} {leaf x} {b}                            = refl
get-set-prop {.(node _)} {.(node _)} {self} {node x x₁} {b}                 = refl
get-set-prop {node xs} {z} {tran {y} (child y∈xs) y⇒z} {node bx txs} {b}    = 
    get-set-prop-help {y} {z} {y⇒z} {xs} {txs} {y∈xs} {b}  
get-set-prop-help {y} {z} {y⇒z} {.(y ∷ _)} {ty ∷ txs} {here} {b}            = 
    get-set-prop {y} {z} {y⇒z} {ty} {b}
get-set-prop-help {y} {z} {y⇒z} {x ∷ xs} {tx ∷ txs} {there y∈xs} {b}        =
    get-set-prop-help {y} {z} {y⇒z} {xs} {txs} {y∈xs} {b}

data _≡ᵖ_ : ∀ {x y z : TreeShape} → x ⇒ y → x ⇒ z → Set where
    refl : ∀ {x y : TreeShape} {x⇒y : x ⇒ y} → x⇒y ≡ᵖ x⇒y 

_≢ᵖ_ : ∀ {x y z : TreeShape} → x ⇒ y → x ⇒ z → Set
x⇒y ≢ᵖ x⇒z = ¬ (x⇒y ≡ᵖ x⇒z) 

get-set-prop-other  : ∀ {x y z : TreeShape} {x⇒y : x ⇒ y} {x⇒z : x ⇒ z} {tx : Tree x}
                    {b : Bool} → x⇒y ≢ᵖ x⇒z
                    → get-valid? x⇒z (get-set x⇒y tx b) 
                    ≡ get-valid? x⇒z tx 
get-set-other-help  : ∀ {y z a a′ : TreeShape} {xs : List TreeShape} 
                    {txs : TreeList xs} {a′⇒z : a′ ⇒ z} {a⇒y : a ⇒ y} 
                    {a′∈xs : a′ ∈ xs} {a∈xs : a ∈ xs} {b : Bool}
                    →  tran {a} (child a∈xs) a⇒y ≢ᵖ tran {a′} (child a′∈xs) a′⇒z
                    → valid? (get a′⇒z (get-list a′∈xs (get-set-help a∈xs a⇒y txs b)))
                    ≡ valid? (get a′⇒z (get-list a′∈xs txs))
get-set-prop-other {.leaf} {.leaf} {.leaf} {self} {self} {leaf x} {b} x₁ 
    = ⊥-elim (x₁ refl)
get-set-prop-other {.(node _)} {.(node _)} {.(node _)} {self} {self} 
    {node x x₂} {b} x₁ 
    = ⊥-elim (x₁ refl)
get-set-prop-other {.(node _)} {.(node _)} {z} {self} 
    {tran {y} (child x₃) y⇒z} {node x x₂} {b} x₁ 
    = refl
get-set-prop-other {x@(node .(a ∷ _))} {y} {.(node (a ∷ _))} 
    {tran {a} (child here) a⇒y} {self} {node x₂ x₃} {b} x₁ 
    = refl
get-set-prop-other {x@(node .(_ ∷ _))} {y} {.(node (_ ∷ _))} 
    {tran {a} (child (there a∈xs)) a⇒y} {self} {node x₂ x₃} {b} x₁ 
    = refl
{-# CATCHALL #-}
get-set-prop-other {x@(node xs)} {y} {z} 
    {tran {a} (child a∈xs) a⇒y} {tran {a′} (child a′∈xs) a′⇒z} 
    {node b′ txs} {b} x₁ = get-set-other-help {y} {z} {a} {a′} {xs} {txs} {a′⇒z} {a⇒y} {a′∈xs} {a∈xs} {b} x₁
    -- =     -- STOP BEING YELLOW !!!
get-set-other-help {y} {z} {a} {.a} {.(a ∷ _)} {x₂ ∷ x₃} 
    {a⇒z} {a⇒y} {here} {here} {b} x 
    = get-set-prop-other {a} {y} {z} {a⇒y} {a⇒z} {x₂} x₄
    where
        x₄ : a⇒y ≢ᵖ a⇒z
        x₄ refl = x refl
get-set-other-help {y} {z} {a} {a′} {.(a′ ∷ _)} {x₂ ∷ x₃} 
    {a′⇒z} {a⇒y} {here} {there a∈xs} {b} x 
    = refl
get-set-other-help {y} {z} {a} {a′} {.(a ∷ _)} {x₂ ∷ x₃} 
    {a′⇒z} {a⇒y} {there a′∈xs} {here} {b} x 
    = refl
get-set-other-help {y} {z} {a} {a′} {(_ ∷ xs)} {x₂ ∷ x₃} 
    {a′⇒z} {a⇒y} {there a′∈xs} {there a∈xs} {b} x 
    = get-set-other-help {y} {z} {a} {a′} {xs} {x₃} x₄
    where
        x₄ : tran {a} (child a∈xs) a⇒y ≢ᵖ tran {a′} (child a′∈xs) a′⇒z
        x₄ refl = x refl

add : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Tree x
add x y = get-set x y true

add-valid   : ∀ {x y : TreeShape} {tx : Tree x} {x⇒y : x ⇒ y} 
            → valid x⇒y (add x⇒y tx)
add-valid {x} {y} {tx} {x⇒y} = get-set-prop {x} {y} {x⇒y} {tx} {true}

add-valid-other : ∀ {x y z : TreeShape} {x⇒y : x ⇒ y} {x⇒z : x ⇒ z} {tx : Tree x}
                    {b : Bool} → x⇒y ≢ᵖ x⇒z
                    → get-valid? x⇒z (add x⇒y tx) 
                    ≡ get-valid? x⇒z tx 
add-valid-other = get-set-prop-other

remove : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Tree x
remove x y = get-set x y false 

remove-invalid  : ∀ {x y : TreeShape} {tx : Tree x} {x⇒y : x ⇒ y} 
                → invalid x⇒y (remove x⇒y tx)
remove-invalid {x} {y} {tx} {x⇒y} = get-set-prop {x} {y} {x⇒y} {tx} {false}

remove-valid-other : ∀ {x y z : TreeShape} {x⇒y : x ⇒ y} {x⇒z : x ⇒ z} {tx : Tree x}
                    {b : Bool} → x⇒y ≢ᵖ x⇒z
                    → get-valid? x⇒z (remove x⇒y tx) 
                    ≡ get-valid? x⇒z tx 
remove-valid-other = get-set-prop-other
```

## Failed attempts and random pieces of code

```plaintext
-- get-set-other-help {.(node xs)} {z} {a} {a′} {xs} {self} {x⇒z} {tx} {a′⇒z} {a⇒y} {a′∈xs} {a∈xs} {b} x = {!   !}
-- get-set-other-help {y} {z} {a} {a′} {xs} {tran x₁ x⇒y} {x⇒z} {tx} {a′⇒z} {a⇒y} {a′∈xs} {a∈xs} {b} x = {!   !} 
-- get-set-other-help  {y} {z} {a} {a} {xs} {tran {a} (child here) a⇒y} {tran {a} (child here) a⇒z} {node x₂ (x₃ ∷ x₄)}  x₁ = get-set-prop-other {a} {y} {z} {a⇒y} {a⇒z} {x₃}  x₅

--get-set-prop-other {x@(node .(_ ∷ _))} {y} {z} {tran {a} (child (there a∈xs)) a⇒y} {tran x₂ x⇒z} {tx} {b} x₁ = {!   !}


valid : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Set
valid x x₁ = (get-valid? x x₁) ≡ true

get-set-list : ∀ {x : TreeShape} {xs : List TreeShape} 
            → x ∈ xs → TreeList xs → Tree x → TreeList xs 
get-set-list here (_ ∷ x₁) b = b ∷ x₁
get-set-list (there x) (x₁ ∷ x₂) b = x₁ ∷ (get-set-list x x₂ b)

add : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Tree x
add x y = get-set x y true

add-valid : ∀ {x y : TreeShape} {tx : Tree x} {x⇒y : x ⇒ y} 
            → valid x⇒y (add x⇒y tx)
add-valid {.leaf} {.leaf} {leaf x} {self} = refl
add-valid {.(node _)} {.(node _)} {node x x₁} {self} = refl
add-valid {x} {y} {tx} {tran x₁ x⇒y} = {!   !}
```

```plaintext
data TreeShape : Set where
    leaf    : TreeShape
    []      : TreeShape
    _∷_     : TreeShape → TreeShape → TreeShape

data Tree : TreeShape → Bool → Set where
    leaf    : (x : Bool) → Tree leaf x
    []      : (x : Bool) → Tree [] x
    _∷_     : ∀ {x y : TreeShape} {a b : Bool}
            → Tree x a → Tree y b → Tree (x ∷ y) (a ∧ b)

data FSObj : TreeShape → Set where
    file : FSObj leaf
    []   : FSObj []

data _⇒_ : TreeShape → TreeShape → Set where
    here : ∀ {x y : TreeShape} → (y ∷ x) ⇒ y 
    there : ∀ {x y z : TreeShape} → x ⇒ y → (z ∷ x) ⇒ y 

ex : TreeShape
ex = (leaf ∷ leaf ∷ []) ∷ [] 
```

```plaintext
data TreeShape : Set where
    leaf    : TreeShape
    node    : List TreeShape → TreeShape

data TreeList : List TreeShape → Bool → Set
data Tree : TreeShape → Bool → Set

data TreeList where
    []  : (x : Bool) → TreeList [] x
    _∷_ : ∀ {x : TreeShape} {xs : List TreeShape} {a b : Bool} 
            → Tree x a → TreeList xs b → TreeList (x ∷ xs) (a ∧ b)  

data Tree where
    leaf    : (x : Bool) → Tree leaf x
    node-in : ∀ {x : Bool} {ts : List TreeShape} 
            → TreeList ts x → Tree (node ts) true 
    node-no : ∀ {ts : List TreeShape} → TreeList ts false → Tree (node ts) false

data _∈_ : TreeShape → List TreeShape → Set where
    here    : ∀ {x : TreeShape} {xs : List TreeShape} → x ∈ (x ∷ xs)
    there   : ∀ {x y : TreeShape} {xs : List TreeShape} 
            → x ∈ xs → x ∈ (y ∷ xs)

data _∈ᶜ_ : TreeShape → TreeShape → Set where
    child   : ∀ {t : TreeShape} {ts : List TreeShape} 
            → (t ∈ ts) → t ∈ᶜ (node ts) 

data _⇒_ : TreeShape → TreeShape → Set where
    self    : ∀ {t : TreeShape} → t ⇒ t
    tran    : ∀ {y x z : TreeShape} → y ∈ᶜ x → y ⇒ z → x ⇒ z
```
```plaintext
find : ∀ {x y : TreeShape} {b : Bool} → Tree x b → x ⇒ y → Bool 
find (leaf b) self = b
find (node-in _) self = true
find (node-in ([] _)) (tran (child ()) x₁)
find (node-in (x₂ ∷ x₃)) (tran (child here) x₁) = find x₂ x₁
find (node-in (x₂ ∷ x₃)) (tran (child (there x)) x₁) = {!   !}
find (node-no x) _ = false

ex-ts : TreeShape
ex-ts = node ((node []) ∷ leaf ∷ [])

-- invalid membership won't typecheck
-- ex-t : Tree ex-ts true
-- ex-t = node-in (node-no ([] true) ∷ leaf true ∷ [] false)

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

```plaintext
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

For specification 2: (the `add` operation)

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

For specification 3: (the `remove` operation)

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

Well founded relations 

(The following can be found in `Induction.WellFounded`, just playing around)

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

leaf-⊀ : ∀ {x} → x ≺ leaf → ⊥
leaf-⊀ (trans _ p) = leaf-⊀ p

node-[]-⊀ : ∀ {xs} → xs ≺ node [] → ⊥
node-[]-⊀ (child (inᶜ ()))
node-[]-⊀ (trans x p) = node-[]-⊀ p

-- We should show ≺ is wellfounded?

Some attempts

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