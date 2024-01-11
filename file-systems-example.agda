module file-systems-example where

open import file-systems

open import Data.List using (List; _++_; foldr; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

f : Obj
f = file

d : Obj
d = (dir (f ∷ [])) 

root : Obj
root = (dir (d ∷ f ∷ []))

{-
root -- d -- f
    |-- f
-}

{- f is a child of d -}
cfd : Child f d
cfd = evi ici

{- d is a child of root -}
cdr : Child d root 
cdr = evi ici

{- d is the parent of f -}
pdf : Parent d f
pdf = evi cfd

isDir-d : isDir d
isDir-d = evi

root⇒d : root ⇒ d
root⇒d = ici cdr

root′ : Obj
root′ = (dir ((dir (f ∷ f ∷ [])) ∷ f ∷ []))

_ : (add root⇒d isDir-d f) ≡ root′
_ = refl 