```agda
{-# OPTIONS --safe #-}

module FileSystem where

open import Data.List
open import Data.List.NonEmpty
open import Data.Product using (Σ; _×_; _,_)
--open import Data.Maybe
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong)
open import Relation.Nullary using (¬_)
open import Data.Bool
```

# Trees

To model file systems, first we write down what interface we expect
them to satisfy, then we may try to provide a concrete model.

Specification:
1. A FileSystem is abstract (i.e. not concrete)
2. A File System has two main concepts:
  a. directories
  b. files
3. files live 'in' a directory (its parent)
4. directories may also live in another directory (its parent)
5. there is a root directory that has no parent
6. a directory is valid if its eventual parent is the root directory
7. a file is valid if it is in a valid directory
8. one can add files and directories to a file system (and get a new fs)
9. one can remove files and directories from a fs (and get a new fs)
10. adding X to an FS and then immediately deleting it yiels an equivalent fs
11. a derived concept is that of path, which is the inverse graph of 'parent'

```agda
data ParentOrRoot (P : Set) : Set where
  Parent : P → ParentOrRoot P
  Root : ParentOrRoot P

walk : {P C : Set} → (P → C) → C → ParentOrRoot P → C
walk f c (Parent x) = f x
walk f c Root = c

record StaticFileSystem (Directory : Set) (File : Set) : Set₁ where
  field
    f-parent : File → ParentOrRoot Directory
    d-parent : Directory → ParentOrRoot Directory
    root : Directory
    root-is-root : d-parent root ≡ Root
    root-unique : ∀ d → d-parent d ≡ Root → d ≡ root
  -- a path to the root, non-empty as it includes itself
  RootPath : Set
  RootPath = List⁺ Directory

  FSItem : Set
  FSItem = File ⊎ Directory
  
  field
    -- given to us, not computed
    d-rootpath : Directory → RootPath
    f-rootpath : File → RootPath

    is-in : FSItem → Bool
    
  rootpath : FSItem → RootPath
  rootpath (inj₁ f) = f-rootpath f
  rootpath (inj₂ d) = d-rootpath d
  
  path-parent : RootPath → ParentOrRoot Directory
  path-parent (_ ∷ []) = Root
  path-parent (_ ∷ (x ∷ rest)) = Parent x

  -- need to play games to appease termination checker
  d-valid-path : RootPath → Set
  d-valid-path′ : List Directory → Set
  
  d-valid-path (p ∷ []) = d-parent p ≡ Root
  d-valid-path (p ∷ x ∷ xs) = (d-parent p ≡ Parent x) × d-valid-path′ (x ∷ xs)

  d-valid-path′ [] = ⊤
  d-valid-path′ (x ∷ []) = d-parent x ≡ Root
  d-valid-path′ (x ∷ xs@(y ∷ ys)) = d-parent x ≡ Parent y × d-valid-path′ xs
```

```agda
module _ {D F : Set} (fs : StaticFileSystem D F) where
  open StaticFileSystem fs
  
  record ValidFSItem : Set where
    field
      item : FSItem
      valid : d-valid-path (rootpath item)

```

```
record FileSystem : Set₁ where
  open StaticFileSystem
  open ValidFSItem
  
  field
    d-root-path-valid : {D F : Set} (fs : StaticFileSystem D F) (d : D) →
      d-valid-path fs (d-rootpath fs d)
    p-root-path-valid : {D F : Set} (fs : StaticFileSystem D F) (f : F) →
      d-valid-path fs (f-rootpath fs f)

    -- add items already known to potentially exist
    add : {D F : Set} (fs : StaticFileSystem D F) → ValidFSItem fs →
      StaticFileSystem D F

    add-coherent : {D F : Set} (fs : StaticFileSystem D F) →
      (i : ValidFSItem fs) →
      is-in (add fs i) (item i) ≡ true

    remove : {D F : Set} (fs : StaticFileSystem D F) → (i : ValidFSItem fs) →
      is-in fs (item i) ≡ true →
      StaticFileSystem D F

    remove-coherent : {D F : Set} (fs : StaticFileSystem D F) →
      (i : ValidFSItem fs) →
      (isin : is-in fs (item i) ≡ true) →
      is-in (remove fs i isin) (item i) ≡ false 
```

## Toy Example 1

```plaintext
      da
    /    \
  fa      db
         /
        fb
```

```agda
data F : Set where
  fa : F
  fb : F

data D : Set where
  da : D
  db : D

fp : F → ParentOrRoot D
fp fa = Parent da
fp fb = Parent db

dp : D → ParentOrRoot D
dp da = Root
dp db = Parent da

r : D
r = da

rir : dp da ≡ Root
rir = refl

ru : ∀ d → dp d ≡ Root → d ≡ r
ru da x = refl
ru db () 

RP : Set
RP = List⁺ D

FI : Set
FI = F ⊎ D

dr : D → RP
dr da = da ∷ []
dr db = da ∷ db ∷ []

fr : F → RP
fr fa = da ∷ []
fr fb = da ∷ db ∷ []

ii : F ⊎ D → Bool
ii (inj₁ fa) = true
ii (inj₁ fb) = false
ii (inj₂ da) = true
ii (inj₂ db) = true 

sfs : StaticFileSystem D F
sfs = record { f-parent = fp
  ; d-parent = dp
  ; root = r
  ; root-is-root = rir
  ; root-unique = ru
  ; d-rootpath = dr
  ; f-rootpath = fr
  ; is-in = ii
  }

vfsda : ValidFSItem sfs
vfsda = record { item = (inj₂ da) 
  ; valid = refl
  }


```