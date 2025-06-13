```agda
{-# OPTIONS --guardedness #-}
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.Nat
open import Data.Maybe
open import Data.Bool
open import Interface
open Interface.Interface
open Object
```

# Example: A simple counter

```agda
data CounterInstr : Set where
    incr : CounterInstr
    decr : CounterInstr
    read : CounterInstr

data Status : Set where
    success : Status
    failure : Status

Counter : Interface
Counter .Question = CounterInstr
Counter .Answer incr = Status
Counter .Answer decr = Status
Counter .Answer read = ℕ

counter : ℕ → Object Counter
counter n .call incr = (success , counter (suc n))
counter n .call decr = (success , counter (pred n)) 
counter n .call read = (n , counter n)

test0 : Answers _ _
test0 = observe (incr ∷ incr ∷ decr ∷ read ∷ []) (counter 0)
```

The normalizing form of test should be `success ∷ (success ∷ (success ∷ (1 ∷ [])))`

# Example : Non-Repeating Lists

This example implements non-repeating lists (sequences) as interfaces.

```agda
data Seq : Set where
    nil : Seq
    con : ℕ → Seq → Seq

data SeqQs : Set where
    addQ : ℕ → SeqQs
    remQ : ℕ → SeqQs
    read : SeqQs

SeqI : Interface
SeqI .Question = SeqQs
SeqI .Answer (addQ _) = Status
SeqI .Answer (remQ _) = Status
SeqI .Answer (read) = Seq
```

The questions you can ask to `SeqI`:
- `addQ`: add a number to the end of the sequence. Will fail if the number
is already present in the sequence
- `remQ`: remove a number from the sequence. Will fail if the number
is not present in the sequence
- `read`: read out the sequence

```agda
eq? : ℕ → ℕ → Bool
eq? zero zero = true
eq? zero (suc _) = false
eq? (suc _) zero = false
eq? (suc m) (suc n) = eq? m n

in? : ℕ → Seq → Bool
in? m nil = false
in? m (con n ns) with eq? m n
...                 | true = true
...                 | false = in? m ns
```

`eq?` compares two integers, while `in?` judges whether a number
is present in a sequence

```agda
add : ℕ → Seq → Status × Seq
add n s = if (in? n s) then (failure , s) else (success , (con n s))

remove : ℕ → Seq → Status × Seq
remove m nil = (failure , nil)
remove m (con n ns) with eq? m n
...                     | true = (success , ns)
...                     | false = let rs = (remove m ns) 
                                in (proj₁ rs , con n (proj₂ rs))

seq : Seq → Object SeqI
seq s .call (addQ m) = let rs = add m s in (proj₁ rs , seq (proj₂ rs))
seq s .call (remQ m) = let rs = remove m s in (proj₁ rs , seq (proj₂ rs))
seq s .call (read) = (s , seq s)
```

`add` and `remove` performs the actual task and wraps the status and value together.
This simplified the implementation of the object function.

```agda
testSeq : Answers _ _
testSeq = observe ((addQ 1) ∷ (addQ 3) ∷ (addQ 4) ∷ (remQ 2) ∷ (addQ 3) ∷ (remQ 1) ∷ (read) ∷ []) (seq nil)
```

The normal form of `testSeq` is 
```plain
success ∷ (success ∷ (success ∷ (failure ∷ (failure ∷ (success ∷ 
(con 4 (con 3 nil) ∷ []))))))
``` 

# Example: Trees

```
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Tree
open import Interface
open Interface.Interface
open Object
```

```agda
data Either (A : Set) (B : Set) : Set where
    fst : A → Either A B
    snd : B → Either A B

case_of_ : ∀ {A B : Set} → A → (A → B) → B
case x of f = f x
```

## Interface for a file system

To package APIs, we need to 'hide' the `erased` objects from the interface.
This can be achieved by using ℕ to index live files only.

`Maybe` is not proof friendly, but I assume we don't need to reason about
those functions at this level.

```agda
Path : Set
Path = List ℕ

-- this exists in Data.Maybe but it is named 'map' and
-- we already have a function called `map`...
mapᵐ : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B 
mapᵐ f (just x) = just (f x)
mapᵐ f nothing = nothing

-- this exists in Data.List but it is named 'map' and...
mapˡ : ∀ {A B : Set} → (A → B) → List A → List B
mapˡ f [] = []
mapˡ f (x ∷ xs) = f x ∷ mapˡ f xs

-- convert an integer into a membership relation
-- this is to hide erased elements 
ℕ-∈ : ∀ {xs} → ℕ → TreeList xs → Maybe (Σ[ x ∈ TreeShape ] x ∈ xs)
ℕ-∈ zero [] = nothing
ℕ-∈ (suc n) [] = nothing
ℕ-∈ {x ∷ _} zero (tx ∷ txs) with status tx 
... | live = just (x , here)
... | erased = mapᵐ (λ (x , x∈xs) → x , there x∈xs) (ℕ-∈ zero txs)
ℕ-∈ m@(suc n) (tx ∷ txs) with status tx 
... | live = mapᵐ (λ (x , x∈xs) → x , there x∈xs) (ℕ-∈ n txs)
... | erased = mapᵐ (λ (x , x∈xs) → x , there x∈xs) (ℕ-∈ m txs)

-- convert a list of Nat to a ⇒ 
Path-⇒ : ∀ {x} → Path → Tree x → Maybe (Σ[ y ∈ TreeShape ] x ⇒ y)
Path-⇒ {x} [] _ = just (x , self)
Path-⇒ {leaf} (n ∷ ns) tx = nothing
Path-⇒ (n ∷ ns) (node _ txs) with ℕ-∈ n txs
... | just (x , x∈xs) = mapᵐ (λ (y , x⇒y) → y , tran (child x∈xs) x⇒y) 
        (Path-⇒ ns (get-list x∈xs txs))
... | nothing = nothing

-- saying something is live using Path only
path-live : ∀ {x} → Path → Tree x → Set
path-live p tx = mapᵐ (λ (y , x⇒y) → get-status x⇒y tx) (Path-⇒ p tx) ≡ just live

-- innocent helper function
contra : (nothing ≡ just live) → ⊥
contra ()

-- a decidable algorithm for path-live (path-live?)
-- so that when calling the interface it can be decided whether
-- the operation will fail
pl? : ∀ {x} → (p : Path) → (tx : Tree x) → Dec (path-live p tx)
pl? p tx with Path-⇒ p tx 
... | just (y , x⇒y) = res
        where
            res : Dec (just (get-status x⇒y tx) ≡ just live)
            res with get-status x⇒y tx 
            ... | live = yes refl
            ... | erased = no λ ()
... | nothing = no contra

-- extract ⇒ from path-live 
-- i.e. when we know something is live in that location,
-- the path must be pointing to something
pl-⇒ : ∀ {x} → (p : Path) → (tx : Tree x) → path-live p tx 
    → Σ[ y ∈ TreeShape ] x ⇒ y
pl-⇒ {x} [] tx pl = x , self
pl-⇒ nO@(n ∷ ns) tO@(node _ txs) pl with ℕ-∈ n txs 
... | just (x , x∈xs) = proj₁ res , tran (child x∈xs) (proj₂ res)
        where
            tx = get-list x∈xs txs
            -- pl′ should be derived from the strong extensionality
            -- of path-live but I don't know how to write the top-level
            -- signature of that proof...
            pl′ : path-live ns tx
            pl′ with Path-⇒ ns tx
            ... | just (y , x⇒y) = pl
            ... | nothing = ⊥-elim (contra pl) 
            res : Σ[ y ∈ TreeShape ] x ⇒ y
            res = pl-⇒ ns tx pl′
... | nothing = ⊥-elim (contra pl)

-- extract is-live (L) from path-live
-- is-live (L) is what was used in Tree.lagda.md
pl-L : ∀ {x} → (p : Path) → (tx : Tree x) → (pl : path-live p tx) 
    → L (proj₂ (pl-⇒ p tx pl)) tx
pl-L [] tx pl with status tx in eq
... | live = refl
... | erased = ⊥-elim (contradiction pl)
        where 
            contradiction : just erased ≡ just live → ⊥
            contradiction ()
pl-L (n ∷ ns) (node _ txs) pl with ℕ-∈ n txs
-- a little bit of hacking with '_'... 
-- (I don't know what I'm suppose to write here, but agda knows!) 
... | just (x , x∈xs) = pl-L ns tx _
        where
            tx = get-list x∈xs txs
... | nothing = ⊥-elim (contra pl)

-- another innocent helper function
≡-N : ∀ {xs} {x} → x ≡ node xs → N x
≡-N refl = node 
```

Having a way to refer to FS locations without caring about erased files,
we can implement the interface.

```agda
data State : Set where
    success : State
    -- error message
    failure : String → State

data FSQs : Set where 
    -- adding a (sub-)fs
    -- to add a fs, we need a path and a valid fs
    adq : ∀ {a} {ta : Tree a} → Path → V ta → FSQs
    -- removing a (sub-)fs
    -- to remove a fs, we need a path
    req : Path → FSQs
    -- calling this function will evoke garbage collection
    gcq : FSQs
    -- get an object by path
    geq : Path → FSQs
    -- readout the current FS
    print : FSQs

FSI : Interface
FSI .Question = FSQs
FSI .Answer (adq _ _) = State
FSI .Answer gcq = State
FSI .Answer (req _) = State
FSI .Answer print = Σ[ x ∈ TreeShape ] Tree x
-- get might produce an object, or an error message
FSI .Answer (geq _) = Either (Σ[ x ∈ TreeShape ] Tree x) State

-- A file system is a valid tree, literally :)
FS : ∀ {x} {tx : Tree x} → V tx → Object FSI
-- This function works very well with functions from 'Tree'!
FS {x} {tx} Vtx .call (req p) with Path-⇒ p tx
... | just (y , x⇒y) = success , FS (erase-V x⇒y tx Vtx)
... | nothing = failure "Invalid path provided" , FS Vtx
FS {x} {tx} Vtx .call gcq with status tx in eq
... | live = success , FS (All-L′-V (gc-live tx eq))
... | erased = failure "cannot garbage collect erased root" , FS Vtx
FS {x} {tx} Vtx .call (adq {a} {ta} p Vta) with x in eq₁
-- decision branch 0: is the whole fs just a single leaf?
... | node xs = step₁
    where 
    -- decision branch 1: is the path pointing to a live file?
        step₁ : State × Object FSI
        step₁ with pl? p tx 
        ... | yes pl = step₂
            where
            -- decision branch 2: is the path pointing to a node?
                step₂ : State × Object FSI
                step₂ with proj₁ (pl-⇒ p tx pl) in eq₂
                ... | node _ = success , 
                        FS (add-V {node xs} {proj₁ (pl-⇒ p tx pl)} 
                        {node} {≡-N eq₂} 
                        (proj₂ (pl-⇒ p tx pl)) Vtx Vta (pl-L p tx pl))
                ... | leaf = failure "Path is valid, but does not point to a directory" , FS Vtx
        ... | no _ = failure "Invalid path provided" , FS Vtx
... | leaf = failure "FS is a single file" , FS Vtx
FS {x} {tx} Vtx .call print = (x , tx) , FS Vtx
FS {x} {tx} Vtx .call (geq p) with pl? p tx
... | yes pl = fst (proj₁ res , get (proj₂ res) tx) , FS Vtx
        where
            res : Σ[ y ∈ TreeShape ] x ⇒ y
            res = pl-⇒ p tx pl
... | no _ = snd (failure "Invalid path provided") , FS Vtx 
```

## Playground

```agda
-- an empty directory
ed : Tree (node [])
ed = node live []

-- a single file
sf : Tree leaf
sf = leaf live

-- proof that empty directories are valid
ed-V : V ed
ed-V self self = s≤s
ed-V self (tran (child ()) _)
ed-V (tran (child ()) _) _

-- proof that single files are valid
sf-V : V sf
sf-V self self = s≤s

-- let's construct a fs that looks like this!
--       da
--      /  \
--     fa  db
--         /  
--        fb

test : Answers _ _
test = observe ((adq [] ed-V) ∷ (adq [] sf-V) ∷ (adq (1 ∷ []) sf-V) ∷ (adq (0 ∷ []) sf-V) ∷ print ∷ []) (FS ed-V)
```

The normal form for `test` is
```plaintext
success ∷
(success ∷
 (success ∷
  (failure "Path is valid, but points to a node" ∷
   ((node (leaf ∷ node (leaf ∷ []) ∷ []) ,
     node live (leaf live ∷ (node live (leaf live ∷ []) ∷ [])))
    ∷ []))))
```
which is exactly what is expected.

```agda
test′ : Answers _ _
test′ = observe ((adq [] ed-V) ∷ (adq [] sf-V) ∷ (adq (1 ∷ []) sf-V) ∷ 
    (req (1 ∷ [])) ∷ gcq ∷ print ∷ []) (FS ed-V)
```