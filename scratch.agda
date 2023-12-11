module scratch where

open import Data.List using (List; _++_; foldr; []; _∷_)

-- How about making file systems just like trees?
data Obj : Set where
    file : Obj
    dir  : List Obj → Obj

-- The membership relation
data _∈_ : Obj → List Obj → Set where
    ici : ∀ {x : Obj} {xs : List Obj} → x ∈ (x ∷ xs)
    la  : ∀ {x : Obj} {xs : List Obj} → (y : Obj) → x ∈ xs → x ∈ (y ∷ xs)

-- For Obj x and y, we say Child x y if x is a child of y
data Child : Obj → Obj → Set where
    evi : ∀ {x : Obj} {xs : List Obj} → (x ∈ xs) → Child x (dir xs)

-- For Obj x and y, we say Parent y x if we have Child x y
data Parent : Obj → Obj → Set where
    evi : ∀ {x y : Obj} → Child x y → Parent y x

-- The nice relation is now trivial
nice→ : ∀ {x y : Obj} → Child x y → Parent y x
nice→ {x} {y} cxy = evi cxy
nice← : ∀ {x y : Obj} → Parent x y → Child y x
nice← {x} {y} (evi cxy) = cxy

-- For Obj x and y, we say InReach y x if x is in the tree rooted from y
data InReach : Obj → Obj → Set where
    ici : ∀ {x y : Obj} → Child x y → InReach y x
    la  : ∀ {x y z : Obj} → Child y z → InReach y x → InReach z x

data isDir : Obj → Set where
    evi : ∀ {xs : List Obj} → isDir (dir xs) 

-- The MOVE function; Maybe REMOVE should be implemented first
move : ∀ {x y z : Obj} → InReach x y → InReach x z → isDir z → Obj
move {x} {y} {z} (ici (evi y∈cx)) IRxz Dz = dir {!   !} 

-- The LIVE function returns the collection all Objs reachable from an Obj
live : Obj → List Obj
live-help : List Obj → List Obj

live file = file ∷ []
live (dir xs) = ((dir xs) ∷ []) ++ (live-help xs)

live-help [] = []
live-help (x ∷ xs) = (live x) ++ (live-help xs)

