-- a loop model using Fin 8 where even indices = stations, odd indices = tracks
module LoopExampleFin8 where

open import RailSystem
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _*_ ; _≟_ ; _<_ ; _≤_ ; s≤s ; z≤n ; pred)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; <⇒≢ ; ≤∧≢⇒< ; suc-injective)
open import Data.Fin using (Fin ; toℕ ; inject₁; fromℕ<) renaming (zero to fzero ; suc to fsuc)
open import Data.Fin.Properties using (toℕ<n ; toℕ-injective ; toℕ-fromℕ<)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_ ; refl ; cong ; sym ; trans)
open import Relation.Nullary using (¬_)

LoopPosition : Set
LoopPosition = Fin 1000

data Even : ℕ → Set where
    ezero : Even zero 
    esuc : ∀ {n} → Even n → Even (suc (suc n))

data Odd : ℕ → Set where
    oeven : ∀ {n} → Even n → Odd (suc n)

data IsStation : LoopPosition → Set where
    isstation : ∀ {p} → Even (toℕ p) → IsStation p

data IsTrack : LoopPosition → Set where
    isstation : ∀ {p} → Odd (toℕ p) → IsTrack p

data IsLast : LoopPosition → Set where
    islast : ∀ {p} → toℕ p ≡ 999 → IsLast p

isLast? : (p : LoopPosition) → Dec (IsLast p)
isLast? p with toℕ p ≟ 999
... | yes prf = yes (islast prf)
... | no ¬prf = no λ { (islast eq) → ¬prf eq }

help : ∀ {p : LoopPosition} → (toℕ p ≢ 999) → toℕ (fsuc p) < 1000
help {p} ¬eq = ≤∧≢⇒< (toℕ<n p) (λ eq → ¬eq (cong pred eq))

next : LoopPosition → LoopPosition
next p with toℕ p ≟ 999
... | yes _ = fzero
... | no ¬eq = fromℕ< (help {p} ¬eq)

zero≢suc : ∀ {n} → 0 ≡ suc n → ⊥
zero≢suc ()

-- next is injective: if next x ≡ next y then x ≡ y
-- proof by case split on whether x or y are the last element (7).
next-inj : ∀ {x y : LoopPosition} → next x ≡ next y → x ≡ y
next-inj {x} {y} eq with toℕ x ≟ 999 | toℕ y ≟ 999
... | yes p1 | yes p2 = toℕ-injective (trans p1 (sym p2))
... | yes xeq7 | no ¬yeq7 = ⊥-elim (zero≢suc (cong toℕ eq)) 
... | no ¬eq7x | yes _ = ⊥-elim (zero≢suc (cong toℕ (sym eq))) 
... | no ¬eq7x | no ¬eq7y = 
    -- agda, WHAT THE F***?
  let
    nx-eq : toℕ (fromℕ< (help ¬eq7x)) ≡ suc (toℕ x)
    nx-eq = toℕ-fromℕ< (help ¬eq7x)
    ny-eq : toℕ (fromℕ< (help ¬eq7y)) ≡ suc (toℕ y)
    ny-eq = toℕ-fromℕ< (help ¬eq7y)
    sucx-eq-sucy : suc (toℕ x) ≡ suc (toℕ y)
    sucx-eq-sucy = trans (sym nx-eq) (trans (cong toℕ eq) ny-eq)
  in toℕ-injective (suc-injective sucx-eq-sucy)

-- orbit: position after n ticks
orbitFrom : LoopPosition → ℕ → LoopPosition
orbitFrom p zero    = p
orbitFrom p (suc n) = next (orbitFrom p n)

-- orbit injectivity by induction using next-inj
orbitFrom-inj :
  (n : ℕ) → ∀ {x y} → orbitFrom x n ≡ orbitFrom y n → x ≡ y
orbitFrom-inj zero    eq = eq
orbitFrom-inj (suc n) eq = orbitFrom-inj n (next-inj eq)

start0 : LoopPosition
start0 = fzero

start1 : LoopPosition
start1 = fsuc fzero

start0≢start1 : start0 ≢ start1
start0≢start1 ()

-- define trains over Infra with next as the transition
loopInfraFin8 : Infra
loopInfraFin8 = record
  { Resource   = LoopPosition
  ; Transition = LoopPosition
  ; inn        = λ p → p
  ; out        = λ p → next p
  }

train₀ : Train loopInfraFin8
train₀ = record
  { position   = λ n → orbitFrom start0 n
  ; continuous = λ n → step (orbitFrom start0 n)
  }

train₁ : Train loopInfraFin8
train₁ = record
  { position   = λ n → orbitFrom start1 n
  ; continuous = λ n → step (orbitFrom start1 n)
  }

-- main safety thm
pairwiseFin8 : (n : ℕ) → Pairwise-consistent train₀ train₁ n
pairwiseFin8 n eq = start0≢start1 (orbitFrom-inj n eq)
