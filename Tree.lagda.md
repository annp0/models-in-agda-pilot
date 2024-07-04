```agda
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
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
        (1) `as-+`: gives the path to the freshly added subtree
        (2) `as-↑`: lifts an original path to a new path in the
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
| File System   | `V`            |
| Remove        | `erase`        |
| Property (C1) | `erase-V`      |
| Property (C2) | `erase-other`  |
| Add           | `add`          |
| Property (D3) | `add-V`        |
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
-- `map` applys a function to all the nodes in the tree
map : ∀ {x} → (Status → Status) → Tree x → Tree x
map-list : ∀ {xs} → (Status → Status) → TreeList xs → TreeList xs

map f (leaf s) = leaf (f s)
map f (node s l) = node (f s) (map-list f l)
map-list f [] = []
map-list f (tx ∷ txs) = map f tx ∷ map-list f txs
```

Constructs on paths and membership

```agda
data _∈_ : TreeShape → List TreeShape → Set where
    here    : ∀ {x} {xs} → x ∈ (x ∷ xs)
    there   : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

data _≡ᵐ_ : ∀ {x y xs} → x ∈ xs → y ∈ xs → Set where
    refl : ∀ {x xs} {x∈xs : x ∈ xs} → x∈xs ≡ᵐ x∈xs

_≢ᵐ_ : ∀ {x y xs} → x ∈ xs → y ∈ xs → Set
x∈xs ≢ᵐ y∈xs = ¬ (x∈xs ≡ᵐ y∈xs)

-- a decidable algorithm for ≡ᵐ
-- The main purpose of ≡ᵐ, ≡ᵐ?
-- is to concentrate this "pattern" of recursion 
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

-- the 'path' relation
data _⇒_ : TreeShape → TreeShape → Set where
    self : ∀ {t} → t ⇒ t
    tran : ∀ {y x z} → y ∈ᶜ x → y ⇒ z → x ⇒ z

_⇏_ : TreeShape → TreeShape → Set
_⇏_ x y = ¬ (x ⇒ y)

-- compare the path 'chain'
data _≤ᵖ_ : ∀ {x y z} → x ⇒ y → x ⇒ z → Set where
    zero : ∀ {x y} {x⇒x : x ⇒ x} {x⇒y : x ⇒ y} → x⇒x ≤ᵖ x⇒y
    succ : ∀ {x y z a} {y⇒a : y ⇒ a} {y⇒z : y ⇒ z} {y∈x : y ∈ᶜ x} → 
            y⇒a ≤ᵖ y⇒z → (tran y∈x y⇒a) ≤ᵖ (tran y∈x y⇒z)

_≰ᵖ_ : ∀ {x y z} → x ⇒ y → x ⇒ z → Set
x⇒y ≰ᵖ x⇒z = ¬ (x⇒y ≤ᵖ x⇒z)

≤ᵖ-id : ∀ {x y} {x⇒y : x ⇒ y} → x⇒y ≤ᵖ x⇒y
≤ᵖ-id {x} {x} {self} = zero
≤ᵖ-id {x} {z} {tran y∈x y⇒z} = succ ≤ᵖ-id

-- ≤ᵖ is indeed unnecessary since
-- the 'meaning' of x⇒y ≰ᵖ x⇒z is equivalent to y⇏z
-- but I like this definition

-- A basic property for _⇒_
_+ᵖ_ : ∀ {x y z} → x ⇒ y → y ⇒ z → x ⇒ z
self +ᵖ y⇒z = y⇒z
tran a∈xs a⇒y +ᵖ y⇒z = tran a∈xs (a⇒y +ᵖ y⇒z)
```

Properties of a tree

```agda
-- is-node
data N : TreeShape → Set where
    node : ∀ {xs} → N (node xs)

data All (P : ∀ {x} → Tree x → Set) : ∀ {xs} → TreeList xs → Set where
    []  : All P []
    _∷_ : ∀ {x} {tx : Tree x} {xs} {txs : TreeList xs} → P tx → All P txs 
        → All P (tx ∷ txs)
```

Functions to traverse the tree.

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

-- replace an element (of the same shape) in the list (assign-list)
asn-list : ∀ {x xs} → (x∈xs : x ∈ xs) → Tree x → TreeList xs → TreeList xs
asn-list here tx (_ ∷ txs) = tx ∷ txs
asn-list (there x∈xs) tx (ty ∷ txs) = ty ∷ asn-list x∈xs tx txs

-- other elements in the list is unchanged (assign-list-other)
al-other : ∀ {x y xs} {x∈xs : x ∈ xs} {y∈xs : y ∈ xs}
    → x∈xs ≢ᵐ y∈xs → (tx : Tree x) → (txs : TreeList xs) 
    → get-list y∈xs txs ≡ get-list y∈xs (asn-list x∈xs tx txs)
al-other {_} {_} {_} {here} {here} neq _ _ = ⊥-elim (neq refl)
al-other {_} {_} {_} {here} {there y∈xs} neq tx (tz ∷ txs) = refl
al-other {_} {_} {_} {there x∈xs} {here} neq tx (tz ∷ txs) = refl
al-other {_} {_} {_} {there x∈xs} {there y∈xs} neq tx (tz ∷ txs) = 
    al-other neq′ tx txs
    where
        neq′ : x∈xs ≢ᵐ y∈xs
        neq′ refl = neq refl

-- getting the modified element gives the modified element (assign-list-get)
al-get : ∀ {x xs} {tx : Tree x} → (x∈xs : x ∈ xs) → (txs : TreeList xs) 
    → tx ≡ get-list x∈xs (asn-list x∈xs tx txs)
al-get {_} {_} here (tz ∷ txs) = refl
al-get {_} {_} (there x∈xs) (tz ∷ txs) = al-get (x∈xs) txs

-- if the replaced element has the same property, then the `All` property is preserved
All-set : ∀ {x xs} {P : ∀ {z} → Tree z → Set} {tx : Tree x} {txs : TreeList xs}
    → (x∈xs : x ∈ xs) → P tx → All P txs → All P (asn-list x∈xs tx txs)
All-set here Px (_ ∷ axs) = Px ∷ axs
All-set (there x∈xs) Px (az ∷ axs) = az ∷ All-set x∈xs Px axs
```

```agda
-- definition of validity (information flows down on each path)
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

-- construct `All` from arbitrary quantifiers
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
    node s (asn-list y∈xs (erase y⇒z (get-list y∈xs txs)) txs)

-- erase will only decrease the information of a node
erase-↓ : ∀ {x y : TreeShape} → (x⇒y : x ⇒ y) → (tx : Tree x) 
    → status (erase x⇒y tx) ≤ˢ status tx
erase-↓ self (leaf _) = ≤ˢ-min
erase-↓ self (node _ _) = ≤ˢ-min
erase-↓ (tran (child _) _) (node _ _) = s≤s 

erase-V : ∀ {x y : TreeShape} → (x⇒y : x ⇒ y) → (tx : Tree x) 
    → V tx → V (erase x⇒y tx)
erase-V self tx Vx = V-map (↓-↡ ↓h) Vx
-- proof approach: 
-- 1. project to previous `All` properties
-- 2. for each `All` property, reconstruct them for the goal
-- 3. convert those two `All` properties to validity
-- the same goes for add-V
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

-- simplified things with decidables (avoided local induction)
erase-other : ∀ {x y z} → (x⇒y : x ⇒ y) → (x⇒z : x ⇒ z) → x⇒y ≰ᵖ x⇒z
    → (tx : Tree x)
    → get-status x⇒z tx ≡ get-status x⇒z (erase x⇒y tx)
erase-other self x⇒z n tx = ⊥-elim (n zero)
erase-other (tran (child a∈xs) a⇒y) self n (node s _) = refl
erase-other (tran (child a∈xs) a⇒y) (tran (child b∈xs) b⇒z) n (node s txs) 
    with a∈xs ≡ᵐ? b∈xs 
... | yes refl = sym (begin 
        get-status b⇒z (get-list a∈xs (asn-list a∈xs (erase a⇒y a) txs))
    ≡⟨ sym (cong (λ x → get-status b⇒z x) (al-get a∈xs txs)) ⟩
        get-status b⇒z (erase a⇒y a) 
    ≡⟨ sym (erase-other a⇒y b⇒z n′ a) ⟩
        get-status b⇒z a 
    ∎)
    where 
        n′ : a⇒y ≰ᵖ b⇒z
        n′ ≤ = n (succ ≤)
        a = get-list a∈xs txs
... | no neq = cong (λ x → get-status b⇒z x) 
        (al-other neq ((erase a⇒y (get-list a∈xs txs))) txs)
```

For the `add` operation, we need some more help functions.

```agda
-- assign-list on shapes (to change the shape)
-- I have to call it 'set' because I ran out of names...
list-set : ∀ {x xs} → x ∈ xs → TreeShape → List TreeShape
list-set {_} {_ ∷ xs} here y = y ∷ xs
list-set {_} {a ∷ xs} (there x∈xs) y = a ∷ list-set x∈xs y

-- `...-+` gives the path to the new modified object
ls-+ : ∀ {x y xs} → (x∈xs : x ∈ xs) → y ∈ (list-set x∈xs y)
ls-+ here = here
ls-+ (there x∈xs) = there (ls-+ x∈xs)

-- strong extensionality for ≡ᵐ
≡ᵐ-ext : ∀ {x y z xs} {x∈xs : x ∈ xs} {y∈xs : y ∈ xs}
    → x∈xs ≡ᵐ y∈xs 
    → there {x} {z} {xs} x∈xs ≡ᵐ there {y} {z} {xs} y∈xs
≡ᵐ-ext refl = refl

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
        neq′ eq = neq (≡ᵐ-ext eq)

-- add a new element at the head
list-add : TreeShape → List TreeShape → List TreeShape 
list-add x xs = x ∷ xs

la-+ : ∀ {x xs} → x ∈ (list-add x xs)
la-+ = here

la-↑ : ∀ {x y xs} → x ∈ xs → x ∈ (list-add y xs)
la-↑ x∈xs = there x∈xs

-- adding a tree, on shape level
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
-- assign-treelist, on treelists
ls-tree : ∀ {x y xs} → (x∈xs : x ∈ xs) → Tree y 
    → TreeList xs → TreeList (list-set x∈xs y)
ls-tree here ty (_ ∷ txs) = ty ∷ txs
ls-tree (there x∈xs) ty (tx ∷ txs) = tx ∷ ls-tree x∈xs ty txs

-- Given a list with an `all` property, the property is kept
-- if one of its element is replaced by another element
-- with the same propert
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

-- add will not change the information of the node
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
    ls-↑-prop b∈xs c∈xs (λ eq → neq (≡ᵐ-ext eq)) tz txs

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

## Garbage-collect

```agda
-- We need dependent pairs
open import Data.Product

filter : ∀ {xs} → TreeList xs → Σ[ xs′ ∈ List TreeShape ] TreeList xs′
filter [] = [] , []
filter {x ∷ _} (tx ∷ txs) with status tx
... | live = x ∷ proj₁ (filter txs) , tx ∷ proj₂ (filter txs)
... | erased = filter txs

-- garbage-collect function
gc : ∀ {x} → Tree x → Σ[ x′ ∈ TreeShape ] Tree x′
gc-help : ∀ {xs} → TreeList xs → Σ[ xs′ ∈ List TreeShape ] TreeList xs′
gc {leaf} tx = leaf , tx
gc x@{node xs} (node s txs) = node (proj₁ (gc-help txs)) , node s (proj₂ (gc-help txs))
gc-help [] = [] , []
gc-help {x ∷ _} (tx ∷ txs) with status tx
... | live = proj₁ (gc tx) ∷ proj₁ (gc-help txs) , proj₂ (gc tx) ∷ proj₂ (gc-help txs)
... | erased = gc-help txs

-- A quick definition for an all-live tree
-- Could be more general
data All-live : ∀ {x} → Tree x → Set
data All-help : ∀ {xs} → TreeList xs → Set

data All-live where
    leaf : All-live (leaf live)
    node : ∀ {xs} {txs : TreeList xs} → All-help txs → All-live (node live txs) 

data All-help where
    [] : All-help []
    _∷_ : ∀ {x} {xs} {tx : Tree x} {txs : TreeList xs} → All-live tx → All-help txs → All-help (tx ∷ txs)

-- all the children of a tree are live after garbage-collect
gc-live : ∀ {x} → (tx : Tree x) → status tx ≡ live → All-live (proj₂ (gc tx))
gcl-help : ∀ {xs} → (txs : TreeList xs) → All-help (proj₂ (gc-help txs))
gc-live (leaf _) refl = leaf
gc-live (node _ txs) refl = node (gcl-help txs)
gcl-help [] = []
-- after v2.6.3 we have `with ... in ...` now (otherwise I'll be stuck here)
gcl-help (tx ∷ txs) with status tx in eq
... | live = gc-live tx eq ∷ gcl-help txs
... | erased = gcl-help txs
``` 
