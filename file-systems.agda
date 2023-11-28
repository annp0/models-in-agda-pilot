module file-systems where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)

import Data.List using (List; _++_; length; reverse; map; foldr; downFrom)
import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Membership.Propositional using (_∈_)

data File : Set where
    file : File

data Dir : Set where
    dir : Dir

data FSObj : Set where
    fromFile : File -> FSObj
    fromDir : Dir -> FSObj

record FS : Set where
  {- File Systems -}
  field
    live : List FSObj
    {- The collection of FSObjs contained in this FS -}
    root : Dir
    {- The root of the FS -}
    root-live : (fromDir root) ∈ live
    {- The proof that the root is inside live -}
    parent : (x : FSObj) → x ∈ live → ¬ (x ≡ (fromDir root)) → Dir
    {- For each x in live that is not root, we assign it a parent. -}
    parent-live : (x : FSObj) → (lx : x ∈ live) → (nr : ¬ (x ≡ (fromDir root))) → fromDir (parent x lx nr) ∈ live
    {- The parents assigned must also be inside live -}
    content : (x : Dir) → (fromDir x) ∈ live → (FSObj → Bool)
    {- For each directory inside live, we assign them a collection of FSObjs as its content. -}
    parent-content : (x : FSObj) → (lx : x ∈ live) → (nr : ¬ (x ≡ (fromDir root))) → content (parent x lx nr) (parent-live x lx nr) x ≡ true
    {- For all elements of live, it must be in the contents of its parent. -}

    {-
    reachable-from-root : ?
    For all elements of live, it must be reachable from root (be root itself, or be in the contents of root, or be in the contents of contents of root, and so on)
    still thinking of how to implement
    -}