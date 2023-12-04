module file-systems where

open import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)

open import Data.List using (List; _++_; foldr; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_)

data All {A : Set} (P : A → Set) : List A → Set where
    []  : All P []
    _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

data Kind : Set where
    file : Kind
    dir : Kind

data Obj : Kind → Set where
    -- a File has a parent, which is a directory
    file : Obj dir → Obj file
    -- a Dir has a parent, and may contain directories and files
    dir  : Obj dir → List (Obj dir) → List (Obj file) → Obj dir

-- this function returns the parent of a given Obj
parent : ∀ {k : Kind} → Obj k → Obj dir
parent {file} (file p) = p
parent {dir} (dir p _ _) = p

-- those two functions returns the subdirectory and sub files
subDir : Obj dir → List (Obj dir)
subDir (dir _ d f) = d

subFile : Obj dir → List (Obj file)
subFile (dir _ d f) = f

-- the parent of the root is just itself
data isroot : (Obj dir) → Set where
    refl : (x : Obj dir) → (parent x ≡ x) → isroot x

-- an Obj is called nice if it is the child of its parent
data nice : ∀ {k : Kind} → Obj k → Set where
    dir : (x : Obj dir) → x ∈ subDir (parent x) → nice x
    file : (x : Obj file) → x ∈ subFile (parent x) → nice x

-- a directory is called niceDir if all the sub-objects satisfy the nice property
data niceDir : (Obj dir) → Set where
    dir : (x : Obj dir) → All nice (subDir x) → All nice (subFile x) → All niceDir (subDir x) → niceDir x

-- a file system could then be represented by a root that is a niceDir.

-- y is said to be reachable from x if taking parent function over y repeatedly gives x
data reachable : ∀ {k : Kind} → (x : Obj dir) → (y : Obj k) → Set where
    here : ∀ {k : Kind} → (x : Obj dir) → (y : Obj k) → (parent y) ≡ x → reachable x y
    there : ∀ {k : Kind} → (x : Obj dir) → (y : Obj k) → reachable x (parent y) → reachable x y

-- all objects that is reachable from a niceDir are nice
nice : ∀ {k : Kind} → (x : Obj dir) → niceDir x → (y : Obj k) → reachable x y → nice y

-- TODO: implement MOVE and REMOVE