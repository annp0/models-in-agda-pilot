module file-systems where

open import Data.List using (List; _++_; foldr; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)

-- How about making file systems just like trees?
data Obj : Set where
    file : Obj
    dir  : List Obj → Obj

-- The membership relation
data _∈_ : Obj → List Obj → Set where
    ici : ∀ {x : Obj} {xs : List Obj} → x ∈ (x ∷ xs)
    la  : ∀ {x y : Obj} {xs : List Obj} → x ∈ xs → x ∈ (y ∷ xs)

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

-- For Obj x and y, we say InReach y x (y ⇒ x) if x is in the tree rooted from y
-- Actually InReach is the same as Live, so Live is not necessary
data _⇒_ : Obj → Obj → Set where
    soi : ∀ {x : Obj} → (x ⇒ x)
    ici : ∀ {x y : Obj} → Child x y → (y ⇒ x)
    la  : ∀ {x y z : Obj} → Child x y → (x ⇒ z) → (y ⇒ z)

-- An Obj is said to be isDir if it is a directory
data isDir : Obj → Set where
    evi : ∀ {xs : List Obj} → isDir (dir xs) 

-- The filter removes a member of a list, given the proof
filter : (xs : List Obj) → (y : Obj) → (y ∈ xs) → List Obj
filter (x ∷ xs) y (ici) = xs
filter (x ∷ xs) y (la y∈xs) = x ∷ (filter xs y y∈xs)  

-- The Add function adds an Obj to a given directory y
add : ∀ {x y : Obj} → (x ⇒ y) → isDir y → Obj → Obj
add {x} {y} (soi) (evi {xs}) z = dir (z ∷ xs)
add {dir xs} {y} (ici (evi y∈xs)) (evi {ys}) z = dir ((add (soi {y}) (evi {ys}) z) ∷ (filter xs y y∈xs))
add {dir xs} {y} (la {z} (evi z∈xs) zRy) (dy) a = dir ((add zRy dy a) ∷ (filter xs z z∈xs))

-- After adding an Obj to a FS, it is reachable (⇒) from that FS
add⇒ : ∀ {x y z : Obj} → (xRy : x ⇒ y) → (dy : isDir y) → (add xRy dy z) ⇒ z
add⇒ {x} {x} {z} (soi) (evi {xs}) = ici (evi (ici {z} {xs}))
add⇒ {dir xs} {y} {z} (ici (evi y∈xs)) (evi {ys}) = la (evi ici) (add⇒ soi evi)
add⇒ {dir xs} {y} {a} (la {z} (evi z∈xs) zRy) (dy) = la (evi ici) (add⇒ zRy dy)

-- The remove function removes an Obj in a given directory; if the root is removed, return nothing
remove : ∀ {x y : Obj} → x ⇒ y → Maybe Obj
remove-help : ∀ {x y : Obj} → x ⇒ y → Obj
remove {x} {y} (soi) = nothing
remove {x} {y} xRy = just (remove-help xRy)
-- The first pattern of remove-help will never be matched
remove-help {x} {y} (soi) = dir []
remove-help {dir xs} {y} (ici (evi y∈xs)) = (dir (filter xs y y∈xs))
remove-help {dir xs} {y} (la {z} (evi z∈xs) zRy) = (dir ((remove-help zRy) ∷ (filter xs z z∈xs)))

-- The move function moves an Obj to a given directory
-- First add, then remove
-- Moving a parent to its descendants will break some properties
move : ∀ {x y z : Obj} → (x ⇒ y) → (x ⇒ z) → isDir z → Obj
move {x} {y} {z} xRy xRz dz with remove (add⇒ {x} {z} {y} xRz dz)
move {x} {y} {z} xRy xRz dz     | nothing = add xRz dz y
move {x} {y} {z} xRy xRz dz     | just r = r

merge-maybe : Maybe Obj → Maybe Obj → Maybe Obj
merge-maybe nothing nothing = nothing
merge-maybe nothing (just x) = just x
merge-maybe (just y) nothing = just y
merge-maybe (just x) (just y) = just x

open import Data.Bool

eq? : (x : Obj) → (y : Obj) → Bool
eq? file file = true
eq? (dir _) file = false
eq? file (dir _) = false
eq? (dir []) (dir (y ∷ ys)) = false
eq? (dir (x ∷ xs)) (dir []) = false
eq? (dir []) (dir []) = true
eq? (dir (x ∷ xs)) (dir (y ∷ ys)) = (eq? x y) ∧ (eq? (dir xs) (dir ys))  

-- The parent function searches for the parent in a given root 

parent : (x : Obj) → (y : Obj) → Maybe Obj
parent x file = nothing
-- Why this fails the termination checking?
parent x (dir (y ∷ ys)) with eq? x y
...                        | true = just (dir (x ∷ ys))
...                        | false = merge-maybe (parent x y) (parent x (dir ys))
parent x (dir []) = nothing
 