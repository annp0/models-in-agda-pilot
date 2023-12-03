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
  File : Obj dir → Obj file
  -- a Dir has a parent, and may contain directories and files
  Dir  : Obj dir → List (Obj dir) → List (Obj file) → Obj dir

-- this function returns the parent of a given Obj
parent : ∀ {k : Kind} → Obj k → Obj dir
parent {file} (File p) = p
parent {dir} (Dir p _ _) = p

-- those two functions returns the subdirectory and sub files
subDir : Obj dir → List (Obj dir)
subDir (Dir _ d f) = d

subFile : Obj dir → List (Obj file)
subFile (Dir _ d f) = f

-- the parent of the root is just itself
data isroot : (Obj dir) → Set where
  proof-isroot : (x : Obj dir) → (parent x ≡ x) → isroot x

-- an Obj is called nice if it is the child of its parent
data nice : ∀ {k : Kind} → Obj k → Set where
  fromDir : (x : Obj dir) → x ∈ subDir (parent x) → nice x
  fromFile : (x : Obj file) → x ∈ subFile (parent x) → nice x

-- a directory is called niceDir if all the sub-objects satisfy the nice property
data niceDir : (Obj dir) → Set where
  proof-nice : (x : Obj dir) → All nice (subDir x) → All nice (subFile x) → All niceDir (subDir x) → niceDir x 

-- a file system could then be represented by a root that is a niceDir.

-- TODO: implement MOVE and REMOVE