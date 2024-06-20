```agda
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong)
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
    no : ¬ A → Dec A
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
    []      : TreeList []
    _∷_     : ∀ {x : TreeShape} {xs : List TreeShape} 
            → Tree x → TreeList xs → TreeList (x ∷ xs)  

data Tree where
    leaf    : Status → Tree leaf
    node    : ∀ {ts : List TreeShape} 
            → Status → TreeList ts → Tree (node ts) 
```

Our path is independent from the content of the tree.

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

A tree is valid when all the children of an erased node is erased.

```agda
data Not-in : ∀ {x : TreeShape} → Tree x → Set where
    leaf : Not-in (leaf erased)
    node : ∀ {xs : List TreeShape} {txs : TreeList xs} → Not-in (node erased txs)

data Is-node : TreeShape → Set where
    node : ∀ {xs : List TreeShape} → Is-node (node xs)

data Is-in : ∀ {x : TreeShape} → Tree x → Set where
    leaf : Is-in (leaf live)
    node : ∀ {xs : List TreeShape} {txs : TreeList xs} → Is-in (node live txs)

data All : ∀ {xs : List TreeShape} → (∀ {x : TreeShape} → Tree x → Set) → TreeList xs → Set where
    [] : ∀ {P : ∀ {x : TreeShape} → Tree x → Set} → All P []
    _∷_ : ∀ {x : TreeShape} {tx : Tree x} {xs : List TreeShape} {txs : TreeList xs} 
            {P : ∀ {x : TreeShape} → Tree x → Set} → P tx → All P txs → All P (tx ∷ txs)

-- cannot use `All Valid xs` because of termination checking
data All-valid : ∀ {xs : List TreeShape} → TreeList xs → Set 
data Valid : ∀ {x : TreeShape} → Tree x → Set

data Valid where
    leaf        : ∀ {s : Status} → Valid (leaf s)
    node-live   : ∀ {xs : List TreeShape} {txs : TreeList xs} → 
                All-valid txs → Valid (node live txs)
    node-erased : ∀ {xs : List TreeShape} {txs : TreeList xs} →
                All-valid txs → All Not-in txs → Valid (node erased txs)

data All-valid where
    []  : All-valid []
    _∷_ : ∀ {x : TreeShape} {tx : Tree x} {xs : List TreeShape} {txs : TreeList xs}
            → Valid tx → All-valid txs → All-valid (tx ∷ txs)
```

Basic functions to traverse and the content of the tree.

```agda
get-list    : ∀ {x : TreeShape} {xs : List TreeShape} 
            → x ∈ xs → TreeList xs → Tree x 
get-list here (x ∷ _)              = x
get-list (there x∈xs) (_ ∷ xs)     = get-list x∈xs xs 

get : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Tree y 
get self tx                             = tx
get (tran (child y∈xs) y⇒z) (node _ tx) = get y⇒z (get-list y∈xs tx)

status : ∀ {x : TreeShape} → Tree x → Status
status (leaf b)     = b
status (node b _)   = b

get-status : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Status 
get-status x⇒y tx = status (get x⇒y tx)

Is-live : ∀ {x y : TreeShape} → x ⇒ y → Tree x → Set
Is-live x⇒y tx = get-status x⇒y tx ≡ live

-- convert not-in to erased
-- (one would expect this to be trivial, but it turned out not to be the case)
notin-to-erased : ∀ {x y : TreeShape} → (tx : Tree x) → (x⇒y : x ⇒ y)
                    → Not-in (get x⇒y tx) → get-status x⇒y tx ≡ erased
notin-to-erased-help : ∀ {y z : TreeShape} {xs : List TreeShape} → (y⇒z : y ⇒ z)
                    → (y∈xs : y ∈ xs) → (txs : TreeList xs) 
                    → Not-in (get y⇒z (get-list y∈xs txs)) 
                    → get-status y⇒z (get-list y∈xs txs) ≡ erased
notin-to-erased .(leaf erased) self leaf = refl
notin-to-erased .(node erased _) self node = refl
notin-to-erased (node s txs) (tran (child y∈xs) y⇒z) n = notin-to-erased-help y⇒z y∈xs txs n
notin-to-erased-help y⇒z here (tx ∷ txs) n = notin-to-erased tx y⇒z n
notin-to-erased-help y⇒z (there y∈xs) (tx ∷ txs) n =  notin-to-erased-help y⇒z y∈xs txs n
```

The erase function change the status of the node and all of its children
to `erased`.

```agda
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

To state the property of the add operation, we need to
compare paths and memberships.

```agda
data _≡ᵐ_ : ∀ {x y : TreeShape} {xs : List TreeShape} → x ∈ xs → y ∈ xs → Set where
    refl : ∀ {x : TreeShape} {xs : List TreeShape} {x∈xs : x ∈ xs} → x∈xs ≡ᵐ x∈xs

_≢ᵐ_ : ∀ {x y : TreeShape} {xs : List TreeShape} → x ∈ xs → y ∈ xs → Set
x∈xs ≢ᵐ y∈xs = ¬ (x∈xs ≡ᵐ y∈xs)

-- a decidable algorithm
_≡ᵐ?_ : ∀ {x y : TreeShape} {xs : List TreeShape} (x∈xs : x ∈ xs) (y∈xs : y ∈ xs)
        → Dec (x∈xs ≡ᵐ y∈xs)
here ≡ᵐ? here = yes refl
here ≡ᵐ? there y∈xs = no λ ()
there x∈xs ≡ᵐ? here = no λ () 
there x∈xs ≡ᵐ? there y∈xs with x∈xs ≡ᵐ? y∈xs 
... | yes refl = yes refl
... | no neq = no neq′ 
        where
            neq′ : there (x∈xs) ≢ᵐ there (y∈xs)
            neq′ refl = neq refl
``` 

Some operation on lists, and related properties

```agda
list-set : ∀ {x : TreeShape} {xs : List TreeShape} → x ∈ xs → TreeShape → List TreeShape
list-set {_} {_ ∷ xs} here y = y ∷ xs
list-set {_} {a ∷ xs} (there x∈xs) y = a ∷ list-set x∈xs y

-- `...-new` gives the path to the new modified object
list-set-new : ∀ {x y : TreeShape} {xs : List TreeShape} → (x∈xs : x ∈ xs)  
                → y ∈ (list-set x∈xs y)
list-set-new here = here
list-set-new (there x∈xs) = there (list-set-new x∈xs)

eq-help : ∀ {x y z : TreeShape} {xs : List TreeShape} {x∈xs : x ∈ xs} {y∈xs : y ∈ xs}
        → x∈xs ≡ᵐ y∈xs → there {x} {z} {xs} x∈xs ≡ᵐ there {y} {z} {xs} y∈xs
eq-help refl = refl

-- `...-lift` gives the paths to other unmodified objects
-- It 'lifts' the original path to a new path
list-set-lift : ∀ {x y z : TreeShape} {xs : List TreeShape} → (x∈xs : x ∈ xs) → (y∈xs : y ∈ xs) 
                → x∈xs ≢ᵐ y∈xs → y ∈ (list-set x∈xs z)
list-set-lift here here neq = ⊥-elim (neq refl)
list-set-lift here (there y∈xs) neq = there y∈xs
list-set-lift (there x∈xs) here neq = here
list-set-lift (there x∈xs) (there y∈xs) neq = there (list-set-lift x∈xs y∈xs neq′)
    where 
        neq′ : x∈xs ≢ᵐ y∈xs
        neq′ eq = neq (eq-help eq)

-- add a new element at the head
list-add : TreeShape → List TreeShape → List TreeShape 
list-add x xs = x ∷ xs

list-add-new : ∀ {x : TreeShape} {xs : List TreeShape} → x ∈ (list-add x xs)
list-add-new = here

list-add-lift : ∀ {x y : TreeShape} {xs : List TreeShape} → x ∈ xs → x ∈ (list-add y xs)
list-add-lift x∈xs = there x∈xs

add-shape : ∀ {x y : TreeShape} → Is-node x → Is-node y → x ⇒ y → TreeShape → TreeShape
add-shape {node xs} node node self z = node (list-add z xs)
add-shape {node xs} node node (tran {leaf} (child y∈xs) (tran () y⇒z)) a
add-shape {node xs} node node (tran {node x} (child y∈xs) y⇒z) a = node (list-set y∈xs (add-shape node node y⇒z a))
```

We need to state the lift property for `add-shape`.
Since add-shape modifies objects along the path,
we need a relation `(a → b) ≤ᵖ (a → b → c → ...)`

```agda
data _≤ᵖ_ : ∀ {x y z : TreeShape} → x ⇒ y → x ⇒ z → Set where
    zero : ∀ {x y : TreeShape} {x⇒x : x ⇒ x} {x⇒y : x ⇒ y} → x⇒x ≤ᵖ x⇒y
    succ : ∀ {x y z a : TreeShape} {y⇒a : y ⇒ a} {y⇒z : y ⇒ z} {y∈x : y ∈ᶜ x} → 
            y⇒a ≤ᵖ y⇒z → (tran y∈x y⇒a) ≤ᵖ (tran y∈x y⇒z)

_≰ᵖ_ : ∀ {x y z : TreeShape} → x ⇒ y → x ⇒ z → Set
x⇒y ≰ᵖ x⇒z = ¬ (x⇒y ≤ᵖ x⇒z)
```

Back on the `lift` and `new` properties for `add-shape`

```agda
add-shape-lift : ∀ {x y a : TreeShape} → (ix : Is-node x) → (iy : Is-node y) →
                 (x⇒y : x ⇒ y) → (x⇒a : x ⇒ a) → x⇒a ≰ᵖ x⇒y → (z : TreeShape) → (add-shape ix iy x⇒y z) ⇒ a
add-shape-lift node node self self nleq z = ⊥-elim (nleq zero)
add-shape-lift node node self (tran (child y∈xs) y⇒a) nleq z = tran (child (list-add-lift y∈xs)) y⇒a
add-shape-lift node node (tran {b} (child b∈xs) b⇒y) self nleq z = ⊥-elim (nleq zero)
add-shape-lift node node (tran {leaf} (child b∈xs) (tran () b⇒y)) (tran {c} (child c∈xs) c⇒a) nleq z
add-shape-lift node node (tran {b@(node bs)} (child b∈xs) b⇒y) (tran {c} (child c∈xs) c⇒a) nleq z with (b∈xs ≡ᵐ? c∈xs) 
... | yes refl = let r = add-shape node node b⇒y z
                in tran {r} (child (list-set-new b∈xs)) (add-shape-lift node node b⇒y c⇒a nleq′ z)
                where 
                    nleq′ : c⇒a ≤ᵖ b⇒y → ⊥
                    nleq′ n = nleq (succ n)
... | no neq = tran {c} (child (list-set-lift b∈xs c∈xs neq)) c⇒a

add-shape-new : ∀ {x y : TreeShape} → (ix : Is-node x) → (iy : Is-node y) →
                (x⇒y : x ⇒ y) → (z : TreeShape) → (add-shape ix iy x⇒y z) ⇒ z 
add-shape-new node node self z = tran {z} (child list-add-new) self
add-shape-new node node (tran {leaf} (child y∈xs) (tran () y⇒a)) z
add-shape-new node node (tran {node ys} (child y∈xs) y⇒a) z = 
    let r = add-shape node node y⇒a z
    in tran {r} (child (list-set-new y∈xs)) (add-shape-new node node y⇒a z)
```

With things settled on `TreeShape`, we proceed to `Tree`

```agda
tree-list-set : ∀ {x y : TreeShape} {xs : List TreeShape} → (x∈xs : x ∈ xs) 
                → Tree y → TreeList xs → TreeList (list-set x∈xs y)
tree-list-set here ty (_ ∷ txs) = ty ∷ txs
tree-list-set (there x∈xs) ty (tx ∷ txs) = tx ∷ tree-list-set x∈xs ty txs

add : ∀ {x y z : TreeShape} → (ix : Is-node x) → (iy : Is-node y) → (x⇒y : x ⇒ y) 
        → Tree x → Tree z → Tree (add-shape ix iy x⇒y z)
add node node self (node s txs) tz = node s (tz ∷ txs)
add node node (tran {leaf} (child b∈xs) (tran () b⇒y)) tx tz
add node node (tran {(node bs)} (child b∈xs) b⇒y) (node s txs) tz 
    = node s (tree-list-set b∈xs (add node node b⇒y (get-list b∈xs txs) tz) txs)

-- adding a valid tree to a valid tree gives back a valid tree

add-valid : ∀ {x y z : TreeShape} → (ix : Is-node x) → (iy : Is-node y) → (x⇒y : x ⇒ y) 
        → (tx : Tree x) → (tz : Tree z) → (vx : Valid tx) → (vz : Valid tz)
        → Is-live x⇒y tx → Valid (add ix iy x⇒y tx tz)
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

To prove the final property `add-other`, we need two helper functions.

```agda
-- `list-set-new` gives a path to the freshly modified object
-- `list-set-new-prop` states that this path points to the freshly modified object
list-set-new-prop : ∀ {b} {xs} {c}
    → (b∈xs : b ∈ xs) → (tc : Tree c) → (txs : TreeList xs)
    → tc ≡ get-list (list-set-new b∈xs) (tree-list-set b∈xs tc txs)
list-set-new-prop here tc (tx ∷ txs) = refl
list-set-new-prop (there b∈xs) tc (tx ∷ txs) = list-set-new-prop b∈xs tc txs

-- `list-set-lift` lifts an original path to a path in the modified list, 
--  given that the path pointing to the modified object is different
-- `list-set-new-prop` states that this path points the same object
--  as the previous one
list-set-lift-prop : ∀ {b} {xs} {c} {z}
    → (b∈xs : b ∈ xs) → (c∈xs : c ∈ xs) → (neq : b∈xs ≢ᵐ c∈xs) → (tz : Tree z) → (txs : TreeList xs)
    → get-list c∈xs txs ≡ get-list (list-set-lift b∈xs c∈xs neq) (tree-list-set b∈xs tz txs) 
list-set-lift-prop here here neq tz (tx ∷ txs) = ⊥-elim (neq refl)
list-set-lift-prop here (there c∈xs) neq tz (tx ∷ txs) = refl
list-set-lift-prop (there b∈xs) here neq tz (tx ∷ txs) = refl
list-set-lift-prop (there b∈xs) (there c∈xs) neq tz (tx ∷ txs) = list-set-lift-prop b∈xs c∈xs (λ z → neq (eq-help z)) tz txs

-- the `add` operation won't change the content of other files in the system
add-other : ∀ {x y z a : TreeShape} → (ix : Is-node x) → (iy : Is-node y) → (x⇒y : x ⇒ y) 
        → (x⇒a : x ⇒ a) → (leq : x⇒a ≰ᵖ x⇒y) → (tx : Tree x) → (tz : Tree z)
        → Is-live x⇒y tx 
        → get-status x⇒a tx ≡ 
        get-status (add-shape-lift ix iy x⇒y x⇒a leq z) (add ix iy x⇒y tx tz)
add-other node node self self leq tx tz x = ⊥-elim (leq zero)
add-other node node self (tran (child _) x⇒a) leq (node _ _) tz x = refl
add-other node node (tran (child _) _) self leq (node _ _) tz x = ⊥-elim (leq zero)
add-other node node (tran {leaf} (child _) (tran () _)) (tran (child c∈xs) c⇒a) leq (node s txs) tz x
add-other {_} {_} {z} node node (tran {b@(node bs)} (child b∈xs) b⇒y) (tran (child c∈xs) c⇒a) leq (node s txs) tz x with (b∈xs ≡ᵐ? c∈xs)
... | yes refl = begin 
                    get-status c⇒a tb      
                ≡⟨ add-other node node b⇒y c⇒a leq′ tb tz x ⟩
                    λ′ tb′
                ≡⟨ cong λ′ (list-set-new-prop b∈xs tb′ txs) ⟩
                    refl
                where
                    leq′ : c⇒a ≰ᵖ b⇒y
                    leq′ le = leq (succ le)
                    tb = get-list b∈xs txs
                    λ′ = (λ x → get-status (add-shape-lift node node b⇒y c⇒a (λ le → leq (succ le)) z) x)
                    tb′ = (add node node b⇒y (get-list b∈xs txs) tz)
... | no neq = begin
        get-status c⇒a (get-list c∈xs txs)
        ≡⟨ cong (λ x → get-status c⇒a x) (list-set-lift-prop b∈xs c∈xs neq (add node node b⇒y (get-list b∈xs txs) tz) txs) ⟩
        refl 
```

## Failed attempts and random pieces of code

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

```agda
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