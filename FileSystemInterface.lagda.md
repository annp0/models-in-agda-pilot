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

## Interface (as a record)

```agda
record ISFS (A : Set) : Set₁ where
    field
        -- what is a FSObj?
        FSOBJ : A → Set
        -- what is a directory?
        ISDIR : (a : A) → FSOBJ a → Set
        -- what is root?
        ROOT : (a : A) → FSOBJ a
        -- how do we establish equality between objects?
        ISEQ : (a : A) → FSOBJ a → FSOBJ a → Set 
        -- get children of a directory
        GETC : (a : A) → (obj : FSOBJ a) → ISDIR a obj → List (FSOBJ a)
        -- get the parent
        GETP : (a : A) → (obj : FSOBJ a) → ¬ (ISEQ a obj (ROOT a)) → (FSOBJ a)
        -- removing something
        RM : (a : A) → (obj : FSOBJ a) → ¬ (ISEQ a obj (ROOT a)) → A
        -- adding something
        AD : (a : A) → (obj : FSOBJ a) → ISDIR a (ROOT a) → ISDIR a obj → A → A
        
-- I really ran out of names...
-- FileSystemType
-- A file system is a tree that's valid, and the root is live
FST : Set
FST = Σ[ x ∈ TreeShape ] (Σ[ tx ∈ Tree x ] ((V tx) × (L′ tx)))

-- PATH
PATH : FST → Set
PATH (x , _) = Σ[ y ∈ TreeShape ] x ⇒ y

-- a path is valid if it points to something
-- and that thing is live
PATH-VAL : (fx : FST) → PATH fx → Set
PATH-VAL (_ , (tx , _)) (_ , x⇒y) = L′ (get x⇒y tx) 

-- extract information from a valid path
-- this is not required by the specification given by
-- `IsFS` but since we can do it then why not?
-- in this particular model from a path we can extract a FS 
EXT : (fx : FST) → (p : PATH fx) → PATH-VAL fx p → FST
EXT (_ , (tx , (vx , lx))) (y , x⇒y) pv = y , (get x⇒y tx) , V-∀ x⇒y vx , pv

-- A file system object is a valid path
FSOBJ : FST → Set
FSOBJ fx = Σ[ p ∈ PATH fx ] PATH-VAL fx p

-- Is an object a node?
ISDIR : (fx : FST) → FSOBJ fx → Set
ISDIR fx ((y , _) , pv) = N y

-- get children..
GETC : (fx : FST) → (obj : FSOBJ fx) → ISDIR fx obj → List (FSOBJ fx)
GETC fx@(x , (tx , _)) ((node ys , x⇒y) , pv) node = map-∈ gen-∈ 
    where
        gettl : ∀ {ys} → Tree (node ys) → TreeList ys
        gettl (node _ tys) = tys
        gen-∈ : ∀ {ys} → List (Σ[ x ∈ TreeShape ] x ∈ ys)
        gen-∈ {[]} = []
        gen-∈ {y ∷ ys} = (y , here) ∷ mapˡ 
            (λ (x , x∈xs) → (x , there x∈xs)) (gen-∈ {ys})
        ty = get x⇒y tx
        map-∈ : List (Σ[ x ∈ TreeShape ] x ∈ ys) → List (FSOBJ fx)
        map-∈ [] = []
        map-∈ ((z , z∈ys) ∷ rest) with status (get-list z∈ys (gettl ty)) in eq
        ... | live = ((z , x⇒y +ᵖ tran (child z∈ys) self) , 
            (begin get-status (x⇒y +ᵖ tran (child z∈ys) self) tx 
            ≡⟨ cong status (get-+ᵖ x⇒y (tran (child z∈ys) self) tx) ⟩ 
            get-status (tran (child z∈ys) self) ty 
            ≡⟨ cong status help ⟩
            eq)
            ) ∷ map-∈ rest
            where
                guide : ∀ {ys} → (ty : Tree (node ys)) → ty ≡ node (status ty) (gettl ty)
                guide (node x x₁) = refl
                useguide : ty ≡ node (status ty) (gettl ty)
                useguide = guide ty
                help : get (tran (child z∈ys) self) ty ≡ get-list z∈ys (gettl ty)
                help = begin 
                    get (tran (child z∈ys) self) ty 
                    ≡⟨ cong (get (tran (child z∈ys) self)) useguide ⟩ 
                    refl
        ... | erased = map-∈ rest

root : (fx : FST) → FSOBJ fx
root (x , tx , vx , lx) = (x , self) , lx

-- equality for paths
data _≡ᵖ_ : ∀ {x y z} → x ⇒ y → x ⇒ z → Set where
    refl : ∀ {x y} {x⇒y : x ⇒ y} → x⇒y ≡ᵖ x⇒y

≡ᵖ-trans : ∀ {x y z a} {x⇒y : x ⇒ y} {x⇒z : x ⇒ z} {x⇒a : x ⇒ a} 
    → x⇒y ≡ᵖ x⇒z → x⇒z ≡ᵖ x⇒a → x⇒y ≡ᵖ x⇒a
≡ᵖ-trans refl refl = refl

≡ᵖ-sym : ∀ {x y z} {x⇒y : x ⇒ y} {x⇒z : x ⇒ z} 
    → x⇒y ≡ᵖ x⇒z → x⇒z ≡ᵖ x⇒y
≡ᵖ-sym refl = refl

-- this is so cursed...
≡-≡ᵖ : ∀ {x y a} {x⇒y : x ⇒ y} {x⇒z : x ⇒ y} {x⇒a : x ⇒ a} 
    → x⇒y ≡ x⇒z → x⇒z ≡ᵖ x⇒a → x⇒y ≡ᵖ x⇒a
≡-≡ᵖ refl refl = refl

-- equality for objects, 
-- since our fs objects contain proofs now, we need an equality
-- with proof irrelavance (i.e. simply just don't care about it)
eqo : (fx : FST) → FSOBJ fx → FSOBJ fx → Set
eqo fx ((y , x⇒y) , pf) ((z , x⇒z) , pf′) = y ≡ z × (x⇒y ≡ᵖ x⇒z)

-- help function for get-parent to reverse induction
HELP : ∀ {x z} → (x⇒z : x ⇒ z) → ¬ (x⇒z ≡ᵖ self) 
-- this is even more cursed... but it has to carry the proof...
-- and the proof is crucial
    → Σ[ y ∈ TreeShape ] (Σ[ x⇒y ∈ x ⇒ y ] 
        (Σ[ z∈y ∈ z ∈ᶜ y ] x⇒z ≡ x⇒y +ᵖ tran z∈y self)) 
HELP self neg = ⊥-elim (neg refl)
HELP {x} (tran z∈ᶜx y⇒z) neg with y⇒z in eq
... | self = x , self , z∈ᶜx , refl
... | tran _ _ = let
        -- I'm very surprised that it worked...
            RES_TS , RES_PH , RES_CH , RES_EQ = HELP y⇒z λ eqp → 
                CONTRA (≡ᵖ-trans (≡ᵖ-sym (≡-≡ᵖ eq refl)) eqp)
        in RES_TS , tran z∈ᶜx RES_PH , RES_CH , 
            cong (tran z∈ᶜx) (trans (sym eq) RES_EQ)
        where
            CONTRA : ∀ {x y z a b} → tran {y} {x} {z} a b ≡ᵖ self → ⊥
            CONTRA ()

-- get parent
GETP : (fx : FST) → (obj : FSOBJ fx) → ¬ (eqo fx obj (root fx)) → FSOBJ fx
GETP (x , tx , vx , lx) ((.x , self) , eq) neq = ⊥-elim (neq (refl , refl))
GETP (x , tx , vx , lx) ((_ , x⇒z@(tran _ _)) , lz) neq = let
        y , x⇒y , z∈y , pf = HELP x⇒z λ ()
    in (y , x⇒y) , ≤ˢ-max-eq 
        (≡-≤ˢ (sym lz) 
        (≡-≤ˢ (cong (λ x → get-status x tx) pf) 
        (vx x⇒y (tran z∈y self))))

-- removing an object
RM : (fx : FST) → (obj : FSOBJ fx) → ¬ (eqo fx obj (root fx)) → FST
RM (x , tx , vx , lx) ((x , self) , eq) neq = ⊥-elim (neq (refl , refl))
RM (x , tx@(node _ _) , vx , lx) ((y , x⇒y@(tran (child _) _)) , eq) neq = x , 
    erase x⇒y tx , erase-V x⇒y tx vx , lx

-- adding an object (never thought `add-≡` would be useful here...) 
AD : (fx : FST) → (obj : FSOBJ fx) → ISDIR fx (root fx) → ISDIR fx obj → FST → FST
AD (x , fx , vx , lx) ((y , x⇒y) , ly) node node (a , fa , va , la) 
    = add-shape node node x⇒y a , add x⇒y fx fa , add-V x⇒y vx va ly , 
    trans (add-≡ node node fx fa x⇒y) lx

_ : ISFS FST
_ = record { 
        FSOBJ = FSOBJ
    ;   ISDIR = ISDIR
    ;   ROOT = root
    ;   ISEQ = eqo
    ;   GETC = GETC 
    ;   GETP = GETP
    ;   RM = RM
    ;   AD = AD
    }

```
 