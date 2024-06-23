```agda
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
```

## Specifications

1. A FileSystem is abstract (i.e. not concrete)
2. A File System has two main concepts:
  a. directories
  b. files
3. files live 'in' a directory (its parent)
4. directories may also live in another directory (its parent)
5. there is a root directory that has no parent
6. a directory is valid if its eventual parent is the root directory
7. a file is valid if it is in a valid directory
8. one can add files and directories to a file system (and get a new fs)
9. one can remove files and directories from a fs (and get a new fs)
10. adding X to an FS and then immediately deleting it yiels an equivalent fs
11. a derived concept is that of path, which is the inverse graph of 'parent'

## Interpretation of the specifications

A. A `FileSystem` is modeled as a rose tree, where `directory`
    corresponds to `node` and `file` corresponds to `leaf`. Because of 
    technical difficulties, we cannot just "remove" a subtree
    from a tree. Therefore, we take a compromise: we mark each object in
    the tree with a `Status` in which it indicates whether it is `erased`
    or not. We say a tree is `Valid` when: 
        (1) All of its children is `Valid`
        (2) For every `erased` node, all of its children must be `erased` as well. 
    A `FileSystem` is then a `Valid` `Tree`.
    Specification 1, 2, 3, 4, 5, 6, 7 are automatically satisfied.

B. `Tree` is indexed by `TreeShape`, and `TreeShape` acts as paths.
    This satisfies Specification 11.
    Notice that the paths here also serves as proof of membership.
    (Maybe the advantage of dependent types?)
    
C. "Removing" a tree, in this context, is just marking a node
    as `erased`. We proved:
        (1) `erase` something in a valid tree will return a valid tree
        (2) this operation won't change the content of other files in the system 
    Since no change to the tree structure is made, there is no change on paths.
    This satisfies Specification 9.

D. "Adding" a tree will literally add a new subtree. Therefore, it will
    change the tree structure (`add-shape`). With this function comes with
    two properties:
        (1) `add-shape-new`: gives the path to the freshly added subtree
        (2) `add-shape-lift`: lifts an original path to a new path in the
            new tree
    On tree level, we proved that: 
        (3) adding a valid tree to a valid tree would return
            a valid tree still
        (4) this operation won't change the content of other files in the
            system
    This satisfies Specification 8.

E. Combining (C2) and (D4) gives us Specification 10.

## APIs

| Specification | Implementation |
| ------------- | -------------- |
| Path          | `TreeShape`    |
| Tree Structure| `Tree`         |
| File System   | `Valid`        |
| Remove        | `erase`        |
| Property (C1) | `erase-valid`  |
| Property (C2) | `erase-prop`   |
| Add           | `add`          |
| Property (D3) | `add-valid`    |
| Property (D4) | `add-other`    |

## Implementation

We use the simplified definition of `Dec`.

```agda
data Dec (A : Set) : Set where
    yes : A → Dec A
    no  : ¬ A → Dec A
```

To get a content-independent path, we define the shape of a tree.

```agda
data TreeShape : Set where
    leaf    : TreeShape
    node    : List TreeShape → TreeShape
```

Trees are indexed by TreeShape, just like `Vec Nat` and `Nat`

Must define a new type `TreeList` for a list of trees, since
it needs to be indexed by a list of shapes.

Each node of the tree is marked by `Status`, which indicates
whether the node is live or erased.

```agda 
data Status : Set where
    live    : Status
    erased  : Status

data TreeList : List TreeShape → Set
data Tree : TreeShape → Set

data TreeList where
    []  : TreeList []
    _∷_ : ∀ {x xs} → Tree x → TreeList xs → TreeList (x ∷ xs)  

data Tree where
    leaf : Status → Tree leaf
    node : ∀ {ts} → Status → TreeList ts → Tree (node ts) 
```

There is a natural order on `Status`.

```agda
data _≤ˢ_ : Status → Status → Set where
    s≤s : ∀ {s} → s ≤ˢ s
    e≤l : erased ≤ˢ live  

-- monotone decreasing functions (↓f can only erase objects)
↓ : (Status → Status) → Set
↓ f = ∀ {s} → f s ≤ˢ s 

-- monotone (mathematically)
↡ : (Status → Status) → Set
↡ f = ∀ {a b} → a ≤ˢ b → f a ≤ˢ f b

≡-≤ˢ : ∀ {x y z} → x ≡ y → y ≤ˢ z → x ≤ˢ z
≡-≤ˢ refl leq = leq

≤ˢ-≡ : ∀ {x y z} → x ≤ˢ y → y ≡ z → x ≤ˢ z
≤ˢ-≡ leq refl = leq

tran-≤ˢ : ∀ {a b c} → a ≤ˢ b → b ≤ˢ c → a ≤ˢ c
tran-≤ˢ s≤s b≤c = b≤c
tran-≤ˢ e≤l s≤s = e≤l

refl-≤ˢ : ∀ {a b} → a ≡ b → a ≤ˢ b
refl-≤ˢ refl = s≤s

≤ˢ-max : ∀ {a} → a ≤ˢ live
≤ˢ-max {live} = s≤s
≤ˢ-max {erased} = e≤l

≤ˢ-min : ∀ {a} → erased ≤ˢ a
≤ˢ-min {live} = e≤l
≤ˢ-min {erased} = s≤s

≤ˢ-min-eq : ∀ {a} → a ≤ˢ erased → a ≡ erased
≤ˢ-min-eq s≤s = refl

↓-erased : ∀ {f} → ↓ f → f erased ≡ erased
↓-erased {f} ↓f = ≤ˢ-min-eq ↓f

-- convert from `monotone` that's easy to prove
-- to `monotone` that's more useful
-- this step relies on the fact that we can
-- enumerate `Status`
↓-↡ : ∀ {f} → ↓ f → ↡ f
↓-↡ {f} ↓f = ↡f 
    where 
        ↡f : ∀ {a b} → a ≤ˢ b → f a ≤ˢ f b
        ↡f {live} {live} a≤b = s≤s
        ↡f {erased} {live} a≤b = tran-≤ˢ ↓f ≤ˢ-min
        ↡f {erased} {erased} a≤b = s≤s
```

Mappings on `Status`

Convention on naming:
- `x, y, z` are for treeshapes
- `tx, ty, tz` correspond to `Tree x, Tree y, Tree z`
- `xs, ...` are for treeshape lists
- `txs, ...` are `TreeList xs, ...` respectively.

```agda
map : ∀ {x} → (Status → Status) → Tree x → Tree x
map-list : ∀ {xs} → (Status → Status) → TreeList xs → TreeList xs

map f (leaf s) = leaf (f s)
map f (node s l) = node (f s) (map-list f l)
map-list f [] = []
map-list f (tx ∷ txs) = map f tx ∷ map-list f txs
```

Our path is independent from the content of the tree.

```agda
data _∈_ : TreeShape → List TreeShape → Set where
    here    : ∀ {x} {xs} → x ∈ (x ∷ xs)
    there   : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

data _≡ᵐ_ : ∀ {x y xs} → x ∈ xs → y ∈ xs → Set where
    refl : ∀ {x xs} {x∈xs : x ∈ xs} → x∈xs ≡ᵐ x∈xs

_≢ᵐ_ : ∀ {x y xs} → x ∈ xs → y ∈ xs → Set
x∈xs ≢ᵐ y∈xs = ¬ (x∈xs ≡ᵐ y∈xs)

-- a decidable algorithm for ≡ᵐ
_≡ᵐ?_ : ∀ {x y xs} (x∈xs : x ∈ xs) (y∈xs : y ∈ xs) → Dec (x∈xs ≡ᵐ y∈xs)
here ≡ᵐ? here = yes refl
here ≡ᵐ? there y∈xs = no λ ()
there x∈xs ≡ᵐ? here = no λ () 
there x∈xs ≡ᵐ? there y∈xs with x∈xs ≡ᵐ? y∈xs 
... | yes refl = yes refl
... | no neq = no neq′ 
        where
            neq′ : there (x∈xs) ≢ᵐ there (y∈xs)
            neq′ refl = neq refl

-- this is necessary to expose the lower sturcture (for the termination checker)
data _∈ᶜ_ : TreeShape → TreeShape → Set where
    child : ∀ {t ts} → (t ∈ ts) → t ∈ᶜ (node ts) 

data _⇒_ : TreeShape → TreeShape → Set where
    self : ∀ {t} → t ⇒ t
    tran : ∀ {y x z} → y ∈ᶜ x → y ⇒ z → x ⇒ z

data _≤ᵖ_ : ∀ {x y z} → x ⇒ y → x ⇒ z → Set where
    zero : ∀ {x y} {x⇒x : x ⇒ x} {x⇒y : x ⇒ y} → x⇒x ≤ᵖ x⇒y
    succ : ∀ {x y z a} {y⇒a : y ⇒ a} {y⇒z : y ⇒ z} {y∈x : y ∈ᶜ x} → 
            y⇒a ≤ᵖ y⇒z → (tran y∈x y⇒a) ≤ᵖ (tran y∈x y⇒z)

_≰ᵖ_ : ∀ {x y z} → x ⇒ y → x ⇒ z → Set
x⇒y ≰ᵖ x⇒z = ¬ (x⇒y ≤ᵖ x⇒z)

-- A basic property for _⇒_
_+ᵖ_ : ∀ {x y z} → x ⇒ y → y ⇒ z → x ⇒ z
self +ᵖ y⇒z = y⇒z
tran a∈xs a⇒y +ᵖ y⇒z = tran a∈xs (a⇒y +ᵖ y⇒z)
```

A tree is valid when all the children of an erased node is erased.

```agda
-- is-node
data N : TreeShape → Set where
    node : ∀ {xs} → N (node xs)

data All (P : ∀ {x} → Tree x → Set) : ∀ {xs} → TreeList xs → Set where
    []  : All P []
    _∷_ : ∀ {x} {tx : Tree x} {xs} {txs : TreeList xs} → P tx → All P txs 
        → All P (tx ∷ txs)
```

Basic functions to traverse the content of the tree.

```agda
get-list : ∀ {x xs} → x ∈ xs → TreeList xs → Tree x 
get-list here (x ∷ _) = x
get-list (there x∈xs) (_ ∷ xs) = get-list x∈xs xs 

get : ∀ {x y} → x ⇒ y → Tree x → Tree y 
get self tx = tx
get (tran (child y∈xs) y⇒z) (node _ tx) = get y⇒z (get-list y∈xs tx)

status : ∀ {x} → Tree x → Status
status (leaf s) = s
status (node s _) = s

get-status : ∀ {x y} → x ⇒ y → Tree x → Status 
get-status x⇒y tx = status (get x⇒y tx)

-- is-live
⊙ : ∀ {x y} → (x⇒y : x ⇒ y) → Tree x → Set
⊙ x⇒y tx = get-status x⇒y tx ≡ live

get-all : ∀ {x xs} {P : ∀ {z} → Tree z → Set} {txs : TreeList xs}
    → (x∈xs : x ∈ xs) → All P txs → P (get-list x∈xs txs)
get-all here (atx ∷ _) = atx
get-all (there x∈xs) (_ ∷ atxs) = get-all x∈xs atxs

get-map-list : ∀ {x xs} (f : Status → Status) → (x∈xs : x ∈ xs)
    → (txs : TreeList xs)
    → get-list x∈xs (map-list f txs) ≡ map f (get-list x∈xs txs)
get-map-list f here (tx ∷ txs) = refl
get-map-list f (there x∈xs) (tx ∷ txs) = get-map-list f x∈xs txs

map-status : ∀ {x} → (f : Status → Status) → (tx : Tree x)
    → status (map f tx) ≡ f (status tx)
map-status f (leaf s) = refl
map-status f (node s _) = refl

get-map : ∀ {x y} → (tx : Tree x) → (x⇒y : x ⇒ y) → (f : Status → Status)
    → get-status x⇒y (map f tx) ≡ f (get-status x⇒y tx)
get-map tx self f = map-status f tx
get-map (node s (tx ∷ txs)) (tran (child here) y⇒z) f = get-map tx y⇒z f
get-map (node s (tx ∷ txs)) (tran (child (there y∈xs)) y⇒z) f = begin 
        get-status y⇒z (get-list y∈xs (map-list f txs))
    ≡⟨ cong (λ z → get-status y⇒z z) (get-map-list f y∈xs txs) ⟩ 
        get-status y⇒z (map f (get-list y∈xs txs)) 
    ≡⟨ get-map (get-list y∈xs txs) y⇒z f ⟩
        f (get-status y⇒z (get-list y∈xs txs))
    ∎

get-+ᵖ : ∀ {x y z} (x⇒y : x ⇒ y) (y⇒z : y ⇒ z) (tx : Tree x) 
    → get (x⇒y +ᵖ y⇒z) tx ≡ get y⇒z (get x⇒y tx)
get-+ᵖ self y⇒z tx = refl
get-+ᵖ (tran (child y∈xs) y⇒z) z⇒a (node s txs) = 
    get-+ᵖ y⇒z z⇒a (get-list y∈xs txs)

-- replace an element in the list
set-list : ∀ {x xs} → (x∈xs : x ∈ xs) → Tree x → TreeList xs → TreeList xs
set-list here tx (_ ∷ txs) = tx ∷ txs
set-list (there x∈xs) tx (ty ∷ txs) = ty ∷ set-list x∈xs tx txs

-- other elements in the list unchanged
set-list-other : ∀ {x y xs} {x∈xs : x ∈ xs} {y∈xs : y ∈ xs}
    → x∈xs ≢ᵐ y∈xs → (tx : Tree x) → (txs : TreeList xs) 
    → get-list y∈xs txs ≡ get-list y∈xs (set-list x∈xs tx txs)
set-list-other {_} {_} {_} {here} {here} neq _ _ = ⊥-elim (neq refl)
set-list-other {_} {_} {_} {here} {there y∈xs} neq tx (tz ∷ txs) = refl
set-list-other {_} {_} {_} {there x∈xs} {here} neq tx (tz ∷ txs) = refl
set-list-other {_} {_} {_} {there x∈xs} {there y∈xs} neq tx (tz ∷ txs) = 
    set-list-other neq′ tx txs
    where
        neq′ : x∈xs ≢ᵐ y∈xs
        neq′ refl = neq refl

set-list-get : ∀ {x xs} {tx : Tree x} → (x∈xs : x ∈ xs) → (txs : TreeList xs) 
    → tx ≡ get-list x∈xs (set-list x∈xs tx txs)
set-list-get {_} {_} here (tz ∷ txs) = refl
set-list-get {_} {_} (there x∈xs) (tz ∷ txs) = set-list-get (x∈xs) txs

-- if the replaced element has the same property, then the `All` property is preserved
All-set : ∀ {x xs} {P : ∀ {z} → Tree z → Set} {tx : Tree x} {txs : TreeList xs}
    → (x∈xs : x ∈ xs) → P tx → All P txs → All P (set-list x∈xs tx txs)
All-set here Px (_ ∷ axs) = Px ∷ axs
All-set (there x∈xs) Px (az ∷ axs) = az ∷ All-set x∈xs Px axs
```

```agda
-- definition of validity
V : ∀ {x} → Tree x → Set
V {x} tx = ∀ {y z} → (x⇒y : x ⇒ y) → (y⇒z : y ⇒ z) 
            → get-status (x⇒y +ᵖ y⇒z) tx ≤ˢ get-status x⇒y tx

-- validity is preserved under monotone (↡) mappings
V-map : ∀ {f x} {tx : Tree x} → ↡ f → V tx → V (map f tx)
V-map {f} {_} {tx} ↡f Vx x⇒y y⇒z = ≤ˢ-≡ 
    (≡-≤ˢ (get-map tx (x⇒y +ᵖ y⇒z) f) (↡f (Vx x⇒y y⇒z))) 
    (sym (get-map tx x⇒y f))

-- construct validity from `All` properties
All-V : ∀ {s xs} {txs : TreeList xs} → All (λ tx → status tx ≤ˢ s) txs 
    → All V txs → V (node s txs)
All-V as bs self self = s≤s
All-V as bs self (tran (child y∈xs) y⇒z) = 
    tran-≤ˢ (get-all y∈xs bs self y⇒z) (get-all y∈xs as)
All-V as bs (tran (child y∈xs) y⇒z) z⇒a = get-all y∈xs bs y⇒z z⇒a

-- construct `All` from arbitrary qualifiers
∀-All : ∀ {xs} {txs : TreeList xs} {P : ∀ {y} → Tree y → Set} 
    → (∀ {x} → (x∈xs : x ∈ xs) → P (get-list x∈xs txs)) → All P txs
∀-All {[]} {[]} {P} prop = []
∀-All {x ∷ xs} {tx ∷ txs} {P} prop = prop here ∷ ∀-All prop′
    where
        prop′ : ∀ {y} → (y∈xs : y ∈ xs) → P (get-list y∈xs txs)
        prop′ y∈xs =  prop (there y∈xs)

-- `project` validity to the first `All` property
V-All₁ : ∀ {s xs} {txs : TreeList xs} → V (node s txs) 
    → All (λ tx → status tx ≤ˢ s) txs
V-All₁ Vx = ∀-All λ x∈xs → Vx self (tran (child x∈xs) self) 

-- `project` validity to the second `All` property
V-All₂ : ∀ {s xs} {txs : TreeList xs} → V (node s txs) → All V txs
V-All₂ Vx = ∀-All λ x∈xs → λ x⇒y → λ y⇒z → Vx (tran (child x∈xs) x⇒y) y⇒z  

h : Status → Status
h _ = erased

↓h : ↓ h
↓h {live} = e≤l
↓h {erased} = s≤s

erase : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Tree x
erase self tx = map h tx
erase (tran (child y∈xs) y⇒z) (node s txs) = 
    node s (set-list y∈xs (erase y⇒z (get-list y∈xs txs)) txs)

erase-↓ : ∀ {x y : TreeShape} → (x⇒y : x ⇒ y) → (tx : Tree x) 
    → status (erase x⇒y tx) ≤ˢ status tx
erase-↓ self (leaf _) = ≤ˢ-min
erase-↓ self (node _ _) = ≤ˢ-min
erase-↓ (tran (child _) _) (node _ _) = s≤s 

erase-V : ∀ {x y : TreeShape} → (x⇒y : x ⇒ y) → (tx : Tree x) 
    → V tx → V (erase x⇒y tx)
erase-V self tx Vx = V-map (↓-↡ ↓h) Vx
erase-V (tran (child y∈xs) y⇒z) (node s txs) Vx = All-V 
    (All-set y∈xs ≤y′ ≤xs) (All-set y∈xs (Vy′ Vy) Vxs)
    where
        ty = get-list y∈xs txs
        ty′ = erase y⇒z ty
        Vy′ = erase-V y⇒z ty
        ≤xs = V-All₁ Vx
        Vxs = V-All₂ Vx
        Vy = get-all y∈xs Vxs
        ≤y′ = tran-≤ˢ (erase-↓ y⇒z ty) (get-all y∈xs ≤xs) 

erase-other : ∀ {x y z} → (x⇒y : x ⇒ y) → (x⇒z : x ⇒ z) → x⇒y ≰ᵖ x⇒z
    → (tx : Tree x)
    → get-status x⇒z tx ≡ get-status x⇒z (erase x⇒y tx)
erase-other self x⇒z n tx = ⊥-elim (n zero)
erase-other (tran (child a∈xs) a⇒y) self n (node s _) = refl
erase-other (tran (child a∈xs) a⇒y) (tran (child b∈xs) b⇒z) n (node s txs) 
    with a∈xs ≡ᵐ? b∈xs 
... | yes refl = sym (begin 
        get-status b⇒z (get-list a∈xs (set-list a∈xs (erase a⇒y a) txs))
    ≡⟨ sym (cong (λ x → get-status b⇒z x) (set-list-get a∈xs txs)) ⟩
        get-status b⇒z (erase a⇒y a) 
    ≡⟨ sym (erase-other a⇒y b⇒z n′ a) ⟩
        get-status b⇒z a 
    ∎)
    where 
        n′ : a⇒y ≰ᵖ b⇒z
        n′ ≤ = n (succ ≤)
        a = get-list a∈xs txs
... | no neq = cong (λ x → get-status b⇒z x) 
        (set-list-other neq ((erase a⇒y (get-list a∈xs txs))) txs)
```

Some operation on lists, and related properties

```agda
list-set : ∀ {x xs} → x ∈ xs → TreeShape → List TreeShape
list-set {_} {_ ∷ xs} here y = y ∷ xs
list-set {_} {a ∷ xs} (there x∈xs) y = a ∷ list-set x∈xs y

-- `...-+` gives the path to the new modified object
ls-+ : ∀ {x y xs} → (x∈xs : x ∈ xs) → y ∈ (list-set x∈xs y)
ls-+ here = here
ls-+ (there x∈xs) = there (ls-+ x∈xs)

eq-help : ∀ {x y z xs} {x∈xs : x ∈ xs} {y∈xs : y ∈ xs}
    → x∈xs ≡ᵐ y∈xs 
    → there {x} {z} {xs} x∈xs ≡ᵐ there {y} {z} {xs} y∈xs
eq-help refl = refl

-- `...-↑` gives the paths to other unmodified objects
-- It 'lifts' the original path to a new path
ls-↑ : ∀ {x y z xs} → (x∈xs : x ∈ xs) → (y∈xs : y ∈ xs) → x∈xs ≢ᵐ y∈xs 
    → y ∈ (list-set x∈xs z)
ls-↑ here here neq = ⊥-elim (neq refl)
ls-↑ here (there y∈xs) neq = there y∈xs
ls-↑ (there x∈xs) here neq = here
ls-↑ (there x∈xs) (there y∈xs) neq = there (ls-↑ x∈xs y∈xs neq′)
    where 
        neq′ : x∈xs ≢ᵐ y∈xs
        neq′ eq = neq (eq-help eq)

-- add a new element at the head
list-add : TreeShape → List TreeShape → List TreeShape 
list-add x xs = x ∷ xs

la-+ : ∀ {x xs} → x ∈ (list-add x xs)
la-+ = here

la-↑ : ∀ {x y xs} → x ∈ xs → x ∈ (list-add y xs)
la-↑ x∈xs = there x∈xs

add-shape : ∀ {x y} → N x → N y → x ⇒ y → TreeShape → TreeShape
add-shape {node xs} node node self z = node (list-add z xs)
add-shape {node xs} node node (tran {leaf} (child y∈xs) (tran () _)) a
add-shape {node xs} node node (tran {node x} (child y∈xs) y⇒z) a = 
    node (list-set y∈xs (add-shape node node y⇒z a))
```

Back on the `lift` and `new` properties for `add-shape`

```agda
as-↑ : ∀ {x y Nx Ny a} → (x⇒y : x ⇒ y) → (x⇒a : x ⇒ a) 
    → x⇒a ≰ᵖ x⇒y → (z : TreeShape) → (add-shape Nx Ny x⇒y z) ⇒ a
as-↑ {_} {_} {node} {node} self self n _ = ⊥-elim (n zero)
as-↑ {_} {_} {node} {node} self (tran (child y∈xs) y⇒a) _ _ = 
    tran (child (la-↑ y∈xs)) y⇒a
as-↑ {_} {_} {node} {node} (tran {b} (child b∈xs) b⇒y) self n _ = 
    ⊥-elim (n zero)
as-↑ {_} {_} {node} {node} (tran {leaf} (child b∈xs) (tran () _)) 
    (tran {c} (child c∈xs) c⇒a) _ z
as-↑ {_} {_} {node} {node} (tran {node _} (child b∈xs) b⇒y) 
    (tran (child c∈xs) c⇒a) n z 
    with (b∈xs ≡ᵐ? c∈xs) 
... | yes refl = let r = add-shape node node b⇒y z
        in tran {r} (child (ls-+ b∈xs)) (as-↑ b⇒y c⇒a n′ z)
            where 
                n′ : c⇒a ≤ᵖ b⇒y → ⊥
                n′ ≤ = n (succ ≤)
... | no neq = tran (child (ls-↑ b∈xs c∈xs neq)) c⇒a

as-+ : ∀ {x y Nx Ny} → (x⇒y : x ⇒ y) → (z : TreeShape) 
    → (add-shape Nx Ny x⇒y z) ⇒ z 
as-+ {_} {_} {node} {node} self z = tran {z} (child la-+) self
as-+ {_} {_} {node} {node} (tran {leaf} (child y∈xs) (tran () _)) z
as-+ {_} {_} {node} {node} (tran {node ys} (child y∈xs) y⇒a) z = 
    let r = add-shape node node y⇒a z
    in tran {r} (child (ls-+ y∈xs)) (as-+ y⇒a z)
```

With things settled on `TreeShape`, we proceed to `Tree`

```agda
ls-tree : ∀ {x y xs} → (x∈xs : x ∈ xs) → Tree y 
    → TreeList xs → TreeList (list-set x∈xs y)
ls-tree here ty (_ ∷ txs) = ty ∷ txs
ls-tree (there x∈xs) ty (tx ∷ txs) = tx ∷ ls-tree x∈xs ty txs

lst-all : ∀ {x y xs} {P : ∀ {z} → Tree z → Set} {ty : Tree y} {txs : TreeList xs}
    → (x∈xs : x ∈ xs) → P ty → All P txs → All P (ls-tree x∈xs ty txs)
lst-all here Py (Pz ∷ Pxs) = Py ∷ Pxs
lst-all (there x∈xs) Py (Pz ∷ Pxs) = Pz ∷ lst-all x∈xs Py Pxs

add : ∀ {x y Nx Ny z} → (x⇒y : x ⇒ y) → Tree x → Tree z 
    → Tree (add-shape Nx Ny x⇒y z)
add {_} {_} {node} {node} self (node s txs) tz = node s (tz ∷ txs)
add {_} {_} {node} {node} (tran {leaf} (child b∈xs) (tran () _)) tx tz
add {_} {_} {node} {node} (tran {(node bs)} (child b∈xs) b⇒y) (node s txs) tz 
    = node s (ls-tree b∈xs (add b⇒y (get-list b∈xs txs) tz) txs)

add-≡ : ∀ {x y z} → (Nx : N x) → (Ny : N y) 
    → (tx : Tree x) → (tz : Tree z) → (x⇒y : x ⇒ y) 
    → status (add {_} {_} {Nx} {Ny} x⇒y tx tz) ≡ status tx
add-≡ node node (node x _) tz self = refl
add-≡ node node (node x _) ta (tran {leaf} (child y∈xs) (tran () _)) 
add-≡ node node (node x _) ta (tran {node _} (child y∈xs) y⇒z) = refl

add-V : ∀ {x y Nx Ny z} {tx : Tree x} {tz : Tree z} → (x⇒y : x ⇒ y) 
    → (Vx : V tx) → (Vz : V tz) → ⊙ x⇒y tx
    → V (add {_} {_} {Nx} {Ny} x⇒y tx tz)
add-V {_} {_} {node} {node} {_} {node s txs} self Vx Vz refl 
    = All-V (≤ˢ-max ∷ V-All₁ Vx) (Vz ∷ V-All₂ Vx)
add-V {_} {_} {node} {node} (tran {leaf} (child y∈xs) (tran () y⇒z)) _ _ _
add-V {_} {_} {node} {node} {_} tx@{node s txs} {tz} 
    (tran {node ys} (child y∈xs) y⇒z) Vx Va ⊙z 
    = All-V 
        (lst-all y∈xs 
            (≡-≤ˢ (add-≡ node node (get-list y∈xs txs) tz y⇒z) 
                (Vx self (tran (child y∈xs) self))) 
        (V-All₁ Vx)) 
        (lst-all y∈xs (add-V y⇒z Vy Va ⊙z) Vxs) 
    where
        Vxs = V-All₂ Vx
        Vy = get-all y∈xs Vxs
```

```agda
-- `list-set-new` gives a path to the freshly modified object
-- `list-set-new-prop` states that this path points to the freshly modified object
ls-+-prop : ∀ {b xs c} → (b∈xs : b ∈ xs) → (tc : Tree c) 
    → (txs : TreeList xs) → tc ≡ get-list (ls-+ b∈xs) (ls-tree b∈xs tc txs)
ls-+-prop here tc (tx ∷ txs) = refl
ls-+-prop (there b∈xs) tc (tx ∷ txs) = ls-+-prop b∈xs tc txs

-- `list-set-lift` lifts an original path to a path in the modified list, 
--  given that the path pointing to the modified object is different
-- `list-set-new-prop` states that this path points the same object
--  as the previous one
ls-↑-prop : ∀ {b xs c z} → (b∈xs : b ∈ xs) → (c∈xs : c ∈ xs) 
    → (neq : b∈xs ≢ᵐ c∈xs) → (tz : Tree z) → (txs : TreeList xs)
    → get-list c∈xs txs ≡ get-list (ls-↑ b∈xs c∈xs neq) (ls-tree b∈xs tz txs) 
ls-↑-prop here here neq tz (tx ∷ txs) = ⊥-elim (neq refl)
ls-↑-prop here (there c∈xs) neq tz (tx ∷ txs) = refl
ls-↑-prop (there b∈xs) here neq tz (tx ∷ txs) = refl
ls-↑-prop (there b∈xs) (there c∈xs) neq tz (tx ∷ txs) = 
    ls-↑-prop b∈xs c∈xs (λ z → neq (eq-help z)) tz txs

-- the `add` operation won't change the content of other files in the system
add-other : ∀ {x y} {Nx : N x} {Ny : N y} {z a} → (x⇒y : x ⇒ y) 
    → (x⇒a : x ⇒ a) → (n : x⇒a ≰ᵖ x⇒y) → (tx : Tree x) → (tz : Tree z) 
    → ⊙ x⇒y tx → get-status x⇒a tx ≡ 
    get-status (as-↑ {_} {_} {Nx} {Ny} x⇒y x⇒a n z) (add x⇒y tx tz)
add-other {_} {_} {node} {node} self self n tx tz ⊙x = ⊥-elim (n zero)
add-other {_} {_} {node} {node} self (tran (child _) x⇒a) _ (node _ _) tz ⊙x = refl
add-other {_} {_} {node} {node} (tran (child _) _) self n (node _ _) tz ⊙x = 
    ⊥-elim (n zero)
add-other {_} {_} {node} {node} (tran {leaf} (child _) (tran () _)) _ _ _ _ _
add-other {_} {_} {node} {node} {z} (tran {node bs} (child b∈xs) b⇒y) 
    (tran (child c∈xs) c⇒a) n (node s txs) tz ⊙x with (b∈xs ≡ᵐ? c∈xs)
... | yes refl = begin 
        get-status c⇒a tb      
    ≡⟨ add-other {_} {_} {node} {node} b⇒y c⇒a n′ tb tz ⊙x ⟩
        λ′ tb′
    ≡⟨ cong λ′ (ls-+-prop b∈xs tb′ txs) ⟩
        refl
    where
        n′ : c⇒a ≰ᵖ b⇒y
        n′ ≤ = n (succ ≤)
        tb = get-list b∈xs txs
        λ′ = (λ x → 
            get-status (as-↑ {_} {_} {node} {node} 
                b⇒y c⇒a (λ ≤ → n (succ ≤)) z) x)
        tb′ = (add b⇒y (get-list b∈xs txs) tz)
... | no neq = begin
        get-status c⇒a (get-list c∈xs txs)
        ≡⟨ cong (λ x → get-status c⇒a x) 
            (ls-↑-prop b∈xs c∈xs neq 
                (add b⇒y 
                    (get-list b∈xs txs) tz) txs) ⟩
        refl 
```

## Failed attempts and random pieces of code

The erase function change the status of the node and all of its children
to `erased`.

```plaintext
add-valid-help : ∀ {b z a : TreeShape} {xs : List TreeShape} 
                → (ib : Is-node b) → (iz : Is-node z)
                → (b∈xs : b ∈ xs) → (b⇒z : b ⇒ z)
                → (txs : TreeList xs) → (ta : Tree a) → All-valid txs
                → Valid ta → get-status b⇒z (get-list b∈xs txs) ≡ live
                → All-valid (tree-list-set b∈xs (add ib iz b⇒z (get-list b∈xs txs) ta) txs)
add-erased-help : ∀ {b z : TreeShape} {xs : List TreeShape} → (txs : TreeList xs)
                → (b⇒z : b ⇒ z) → (b∈xs : b ∈ xs) → All-valid txs → All Not-in txs
                → get-status b⇒z (get-list b∈xs txs) ≡ erased
add-valid node node self (node live txs) tz (node-live all) vz refl = node-live (vz ∷ all)
add-valid node node (tran {leaf} (child b∈xs) (tran () b⇒y)) tx tz
add-valid {node xs} {z} {a} node node (tran {node bs} (child b∈xs) b⇒z) (node live txs) ta (node-live atxs) va lz 
    = node-live (add-valid-help node node b∈xs b⇒z txs ta atxs va lz)
add-valid node node (tran {node bs} (child b∈xs) b⇒z) (node erased txs) ta (node-erased all-v all-n) va lz = ⊥-elim (contradiction l=e)
    where
        ez : get-status b⇒z (get-list b∈xs txs) ≡ erased
        ez = add-erased-help txs b⇒z b∈xs all-v all-n 
        l=e : live ≡ erased
        l=e = trans (sym lz) ez
        contradiction : (live ≡ erased) → ⊥
        contradiction ()
add-valid-help node node here b⇒z (tx ∷ txs) ta (atx ∷ atxs) va lz = add-valid node node b⇒z tx ta atx va lz ∷ atxs
add-valid-help node node (there b∈xs) b⇒z (tx ∷ txs) ta (atx ∷ atxs) va lz = atx ∷ add-valid-help node node b∈xs b⇒z txs ta atxs va lz
add-erased-help (tx ∷ txs) b⇒z here (ntx ∷ ntxs) (atx ∷ atxs) = notin-to-erased tx b⇒z (erased-prop tx b⇒z atx ntx) 
add-erased-help (tx ∷ txs) b⇒z (there b∈xs) (vtx ∷ vtxs) (ntx ∷ ntxs) = add-erased-help txs b⇒z b∈xs vtxs ntxs
```

```plaintext
-- `erase-all` erases the entire tree
erase-all : ∀ {x : TreeShape} → Tree x → Tree x
erase-all-help : ∀ {xs : List TreeShape} → TreeList xs → TreeList xs
erase-all (leaf x) = leaf erased
erase-all (node x txs) = node erased (erase-all-help txs)
erase-all-help [] = []
erase-all-help (tx ∷ txs) = (erase-all tx) ∷ (erase-all-help txs)

-- property of erase-all : all children in the erased tree are erased
erase-all-prop : ∀ {x y : TreeShape} → (tx : Tree x) → (x⇒y : x ⇒ y)
                → get-status x⇒y (erase-all tx) ≡ erased
erase-all-prop-help : ∀ {y z : TreeShape} {xs : List TreeShape} 
                → (txs : TreeList xs) 
                → (y⇒z : y ⇒ z) → (y∈xs : y ∈ xs)
                → get-status y⇒z (get-list y∈xs (erase-all-help txs)) ≡ erased
erase-all-prop (leaf _) self = refl
erase-all-prop (node _ _) self = refl
erase-all-prop (node _ txs) (tran (child y∈xs) y⇒z) = erase-all-prop-help txs y⇒z y∈xs
erase-all-prop-help (ty ∷ txs) y⇒z here = erase-all-prop ty y⇒z
erase-all-prop-help (ty ∷ txs) y⇒z (there y∈xs) = erase-all-prop-help txs y⇒z y∈xs

-- property of erase-all : a completely erased tree is valid
erase-all-valid : ∀ {x : TreeShape} → (tx : Tree x) → Valid (erase-all tx)
erase-all-help-not-in : ∀ {xs : List TreeShape} → (txs : TreeList xs) 
                    → All Not-in (erase-all-help txs)
erase-all-help-valid : ∀ {xs : List TreeShape} → (txs : TreeList xs) 
                    → All-valid (erase-all-help txs)
erase-all-valid (leaf x) = leaf
erase-all-valid (node s txs) = node-erased (erase-all-help-valid txs) (erase-all-help-not-in txs)
erase-all-help-valid [] = []
erase-all-help-valid (tx ∷ txs) = erase-all-valid tx ∷ erase-all-help-valid txs
erase-all-help-not-in [] = []
erase-all-help-not-in (leaf _ ∷ txs) = leaf ∷ erase-all-help-not-in txs
erase-all-help-not-in (node _ _ ∷ txs) = node ∷ erase-all-help-not-in txs

erase : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Tree x
erase-list : ∀ {y z : TreeShape} {xs : List TreeShape} 
        → y ⇒ z → y ∈ xs → TreeList xs → TreeList xs
erase self tx = erase-all tx
erase (tran {y} (child y∈xs) y⇒z) (node s txs) = node s (erase-list y⇒z y∈xs txs)
erase-list y⇒z here (tx ∷ txs) = erase y⇒z tx ∷ txs
erase-list y⇒z (there y∈xs) (tx ∷ txs) = tx ∷ erase-list y⇒z y∈xs txs

-- a valid tree, after the erase operation, is still valid
erase-valid : ∀ {x y : TreeShape} → (x⇒y : x ⇒ y) → (tx : Tree x) → Valid tx
                → Valid (erase x⇒y tx)
erase-valid-help-valid : ∀ {y z : TreeShape} {xs : List TreeShape} → (y∈xs : y ∈ xs)
                → (y⇒z : y ⇒ z)
                → (txs : TreeList xs) → All-valid txs → All-valid (erase-list y⇒z y∈xs txs)
erase-valid-help-notin : ∀ {y z : TreeShape} {xs : List TreeShape} → (y∈xs : y ∈ xs)
                → (y⇒z : y ⇒ z)
                → (txs : TreeList xs) → All Not-in txs → All Not-in (erase-list y⇒z y∈xs txs)
erase-valid self tx vtx = erase-all-valid tx
erase-valid (tran (child y∈xs) y⇒z) (node live txs) (node-live all) = node-live (erase-valid-help-valid y∈xs y⇒z txs all)
erase-valid (tran (child y∈xs) y⇒z) (node erased txs) (node-erased all-v all-n) = node-erased (erase-valid-help-valid y∈xs y⇒z txs all-v) (erase-valid-help-notin y∈xs y⇒z txs all-n)
erase-valid-help-valid here y⇒z (tx ∷ txs) (atx ∷ atxs) = erase-valid y⇒z tx atx ∷ atxs
erase-valid-help-valid (there y∈xs) y⇒z (tx ∷ txs) (atx ∷ atxs) = atx ∷ erase-valid-help-valid y∈xs y⇒z txs atxs
erase-valid-help-notin here self ((leaf erased) ∷ txs) (leaf ∷ atxs) = leaf ∷ atxs
erase-valid-help-notin here self ((node erased _) ∷ txs) (node ∷ atxs) = node ∷ atxs
erase-valid-help-notin here (tran (child _) y⇒z) ((node erased _) ∷ txs) (node ∷ atxs) =  node ∷ atxs 
erase-valid-help-notin (there y∈xs) y⇒z (tx ∷ txs) (atx ∷ atxs) = atx ∷ erase-valid-help-notin y∈xs y⇒z txs atxs

-- the erase operation will leave other nodes in the tree unchanged
erase-prop : ∀ {x y z : TreeShape} → (x⇒y : x ⇒ y) → (tx : Tree x) → (x⇒z : x ⇒ z) → ¬ (y ⇒ z) 
            → get-status x⇒z tx ≡ get-status x⇒z (erase x⇒y tx)
erase-prop-help : ∀ {y z c b : TreeShape} {xs : List TreeShape} → (txs : TreeList xs)
            → (b⇒y : b ⇒ y) → (c⇒z : c ⇒ z) → (c∈xs : c ∈ xs) → (b∈xs : b ∈ xs) 
            → ¬ (y ⇒ z)
            → get-status c⇒z (get-list c∈xs txs) ≡ 
            get-status c⇒z (get-list c∈xs (erase-list b⇒y b∈xs txs))
erase-prop self tx x⇒z neg = ⊥-elim (neg x⇒z)
erase-prop (tran (child _) _) (node s _) self neg = refl
erase-prop (tran (child b∈xs) b⇒y) (node s txs) (tran (child c∈xs) c⇒z) neg = erase-prop-help txs b⇒y c⇒z c∈xs b∈xs neg 
erase-prop-help (tx ∷ txs) b⇒y c⇒z here here neg = erase-prop b⇒y tx c⇒z neg
erase-prop-help (tx ∷ txs) b⇒y c⇒z here (there b∈xs) neg = refl
erase-prop-help (tx ∷ txs) b⇒y c⇒z (there c∈xs) here neg = refl
erase-prop-help (tx ∷ txs) b⇒y c⇒z (there c∈xs) (there b∈xs) neg = erase-prop-help txs b⇒y c⇒z c∈xs b∈xs neg

-- For a valid tree with its root erased, all its children are also erased
erased-prop : ∀ {x y : TreeShape} → (tx : Tree x) → (x⇒y : x ⇒ y)
                → Not-in tx → Valid tx → Not-in (get x⇒y tx)
erased-prop-help : ∀ {y z : TreeShape} {xs : List TreeShape} 
                → (y⇒z : y ⇒ z) → (y∈xs : y ∈ xs)
                → (txs : TreeList xs)
                → All-valid txs → All Not-in txs 
                → Not-in (get y⇒z (get-list y∈xs txs))
erased-prop (leaf _) self ntx vtx = ntx
erased-prop (node s []) self ntx vtx = ntx
erased-prop (node s []) (tran (child ()) x⇒y) ntx vtx
erased-prop (node s (tx ∷ txs)) self ntx vtx = ntx
erased-prop (node erased txs@(_ ∷ _)) (tran (child y∈xs) y⇒z) node (node-erased atxs ntxs) = erased-prop-help y⇒z y∈xs txs atxs ntxs 
erased-prop-help y⇒z here (tx ∷ txs) (vtx ∷ vtxs) (ntx ∷ ntxs) = erased-prop tx y⇒z ntx vtx
erased-prop-help y⇒z (there y∈xs) (tx ∷ txs) (vtx ∷ vtxs) (ntx ∷ ntxs) = erased-prop-help y⇒z y∈xs txs vtxs ntxs
```

-- this property is annoying...

```plaintext
get-set         : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Status → Tree x
get-set-help    : ∀ {y z : TreeShape} {xs : List TreeShape} → y ∈ xs 
                → y ⇒ z → TreeList xs → Status → TreeList xs
get-set self (leaf _) b                         = leaf b
get-set self (node _ txs) b                     = node b txs
get-set (tran (child y∈xs) y⇒z) (node bx txs) b = 
    node bx (get-set-help y∈xs y⇒z txs b)
get-set-help here y⇒z (y ∷ xs) b                = 
    get-set y⇒z y b ∷ xs
get-set-help (there y∈xs) y⇒z (x ∷ xs) b        = 
    x ∷ get-set-help y∈xs y⇒z xs b

get-set-prop        : ∀ {x y : TreeShape} → (x⇒y : x ⇒ y) → (tx : Tree x) 
                    → (b : Status) 
                    → get-status x⇒y (get-set x⇒y tx b) ≡ b 
get-set-prop-help   : ∀ {y z : TreeShape} → (y⇒z : y ⇒ z) → (xs : List TreeShape) 
                    → (txs : TreeList xs) → (y∈xs : y ∈ xs) → (b : Status)
                    → get-status y⇒z (get-list y∈xs (get-set-help y∈xs y⇒z txs b)) 
                    ≡ b
-- when we modify the value of root, and the root is a leaf
get-set-prop self (leaf x) b  = refl
-- when we modify the value of root, and the root is a node
get-set-prop self (node _ _) b = refl
-- when we modify the value of a child, we use `get-set-prop-help`
-- to bring it down to the list level
get-set-prop {node xs} {z} 
    (tran (child y∈xs) y⇒z) (node bx txs) b    
    = get-set-prop-help y⇒z xs txs y∈xs b  
-- if the child is right here in the list
get-set-prop-help y⇒z _ (ty ∷ _) here b = get-set-prop y⇒z ty b
-- if the child is in the rest of the list
get-set-prop-help y⇒z (x ∷ xs) (tx ∷ txs) (there y∈xs) b
    = get-set-prop-help y⇒z xs txs y∈xs b
```

Since our paths are dependently typed, we need a separate notion
of equality and inequality. 

```plaintext
data _≡ᵖ_ : ∀ {x y z : TreeShape} → x ⇒ y → x ⇒ z → Set where
    refl : ∀ {x y : TreeShape} {x⇒y : x ⇒ y} → x⇒y ≡ᵖ x⇒y 

_≢ᵖ_ : ∀ {x y z : TreeShape} → x ⇒ y → x ⇒ z → Set
x⇒y ≢ᵖ x⇒z = ¬ (x⇒y ≡ᵖ x⇒z)
```

Now we are ready to show that the `get-set` operation
will leave other files in the system untouched.

```plaintext
get-set-prop-other  : ∀ {x y z : TreeShape} → 
                    (x⇒y : x ⇒ y) → (x⇒z : x ⇒ z) → (tx : Tree x)
                    → (b : Status) → x⇒y ≢ᵖ x⇒z
                    → get-status x⇒z (get-set x⇒y tx b) 
                    ≡ get-status x⇒z tx 
get-set-other-help  : ∀ {y z a a′ : TreeShape} → (xs : List TreeShape) 
                    → (txs : TreeList xs) → (a′⇒z : a′ ⇒ z) → (a⇒y : a ⇒ y)
                    → (a′∈xs : a′ ∈ xs) → (a∈xs : a ∈ xs) → (b : Status)
                    →  tran {a} (child a∈xs) a⇒y ≢ᵖ tran {a′} (child a′∈xs) a′⇒z
                    → get-status a′⇒z (get-list a′∈xs (get-set-help a∈xs a⇒y txs b))
                    ≡ get-status a′⇒z (get-list a′∈xs txs)
-- if y and z are the same node as x, then the path must be equal and
-- hence those cases are impossible
get-set-prop-other self self (leaf _) _ neq = ⊥-elim (neq refl)
get-set-prop-other self self (node _ _) _ neq = ⊥-elim (neq refl)
-- if y is the same node as x, then the rest of the tree is unchanged
get-set-prop-other self (tran (child _) _) (node _ _) _ _ = refl
-- the same goes when z is the same as x
get-set-prop-other (tran (child _) _) self (node _ _) _ _ = refl
-- otherwise we go down to the children list level
get-set-prop-other {node xs}
    (tran {a} (child a∈xs) a⇒y) 
    (tran {a′} (child a′∈xs) a′⇒z) 
    (node _ txs) b neq 
    = get-set-other-help xs txs a′⇒z a⇒y a′∈xs a∈xs b neq
-- if both are on the top of their list respectively,
-- we just use the main proof
get-set-other-help _ (ta ∷ _) a⇒z a⇒y here here b neq 
    = get-set-prop-other a⇒y a⇒z ta b neq′
    where
        neq′ : a⇒y ≢ᵖ a⇒z
        neq′ refl = neq refl
-- if they are at different positions, it is just refl
get-set-other-help (_ ∷ _) (_ ∷ _) 
    a′⇒z a⇒y here (there a∈xs) _ _ = refl
get-set-other-help (_ ∷ _) (_ ∷ _) 
    a′⇒z a⇒y (there a′∈xs) here _ _ = refl
-- if they are both in the rest of their lists, recursively
-- call the help function
get-set-other-help (_ ∷ xs) (_ ∷ txs) 
    a′⇒z a⇒y (there a′∈xs) (there a∈xs) b neq
    = get-set-other-help xs txs a′⇒z a⇒y a′∈xs a∈xs b neq′ 
    where
        neq′ : tran (child a∈xs) a⇒y ≢ᵖ tran (child a′∈xs) a′⇒z
        neq′ refl = neq refl
```


```plaintext
add : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Tree x
add x⇒y tx = get-set x⇒y tx true

add-valid   : ∀ {x y : TreeShape} → (tx : Tree x) → (x⇒y : x ⇒ y) 
            → valid x⇒y (add x⇒y tx)
add-valid {x} {y} tx x⇒y = get-set-prop x⇒y tx true

add-valid-other : ∀ {x y z : TreeShape} → (x⇒y : x ⇒ y) 
                    → (x⇒z : x ⇒ z) → (tx : Tree x)
                    → x⇒y ≢ᵖ x⇒z
                    → get-valid? x⇒z (add x⇒y tx) 
                    ≡ get-valid? x⇒z tx 
add-valid-other x⇒y x⇒z tx neq = get-set-prop-other x⇒y x⇒z tx true neq

remove : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Tree x
remove x⇒y tx = get-set x⇒y tx false 

remove-invalid : ∀ {x y : TreeShape} → 
                (tx : Tree x) → (x⇒y : x ⇒ y) 
                → invalid x⇒y (remove x⇒y tx)
remove-invalid tx x⇒y = get-set-prop x⇒y tx false

remove-valid-other : ∀ {x y z : TreeShape} 
                    → (x⇒y : x ⇒ y) → (x⇒z : x ⇒ z) 
                    → (tx : Tree x)
                    → x⇒y ≢ᵖ x⇒z
                    → get-valid? x⇒z (remove x⇒y tx) 
                    ≡ get-valid? x⇒z tx 
remove-valid-other x⇒y x⇒z tx neq = get-set-prop-other x⇒y x⇒z tx false neq
```


```plaintext

data all-not-in : ∀ {xs : List TreeShape} → TreeList xs → Set where
    []  : all-not-in []
    _∷_ : ∀ {x : TreeShape} {tx : Tree x} {xs : List TreeShape} {txs : TreeList xs}
        → not-in tx → all-not-in txs → all-not-in (tx ∷ txs)
        
data all-is-valid : ∀ {xs : List TreeShape} → TreeList xs → Set 
data is-valid : ∀ {x : TreeShape} → Tree x → Set

data is-valid where
    leaf        : is-valid (leaf live)
    node-yes    : ∀ {xs : List TreeShape} {txs : TreeList xs} → 
                all-is-valid txs → is-valid (node live txs)
    node-no     : ∀ {xs : List TreeShape} {txs : TreeList xs} →
                all-is-valid txs → all-not-in txs → is-valid (node erased txs)

data all-is-valid where
    [] : all-is-valid []
    _∷_ : ∀ {x : TreeShape} {tx : Tree x} {xs : List TreeShape} {txs : TreeList xs}
            → is-valid tx → all-is-valid txs → all-is-valid (tx ∷ txs)



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
  