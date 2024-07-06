```agda
{-# OPTIONS --guardedness #-}
module FileSystemInterface where

open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Tree
open import Interface
open Interface.Interface
open Object
```

```agda
data Either (A : Set) (B : Set) : Set where
    fst : A → Either A B
    snd : B → Either A B
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