module file-systems where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)

open import Data.Bool.Base using (Bool; true)
open import Data.List using (List; _++_; length; reverse; map; foldr; downFrom)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)

-- Want to model a "file system" where we declare that it
-- can contain two kinds of things, files and directories


data Kind : Set where
  file : Kind
  dir : Kind

data FSObj : Kind -> Set where
  -- a File has a parent, which is a directory
  File : FSObj dir -> FSObj file
  -- normal Dir has a parent, and may contain directories and files
  Dir  : FSObj dir -> List (FSObj dir) -> List (FSObj file) -> FSObj dir
  RootDir : List (FSObj dir) -> List (FSObj file) -> FSObj dir

parent : (k : Kind) -> FSObj k -> Maybe (FSObj dir)
parent file (File o) = just o
parent dir (Dir o _ _) = just o
parent dir (RootDir _ _) = nothing

-- A file system has a root object
record FS : Set where
  field
    rootD : FSObj dir
    root-has-no-parent : parent dir rootD ≡ nothing

contents : FSObj dir -> List (FSObj dir) × List (FSObj file)
contents (Dir _ d f) = d , f
contents (RootDir d f) = d , f
