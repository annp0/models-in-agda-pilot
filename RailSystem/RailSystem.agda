module RailSystem where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Fin using (Fin) renaming (zero to fzero ; suc to fsuc)
open import Data.Empty using (⊥ ; ⊥-elim)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_ ; refl)

record Infra : Set₁ where
  field
    Resource    : Set
    Transition  : Set
    inn         : Transition → Resource
    out         : Transition → Resource

open Infra

data Adjacent (N : Infra) : (x y : N .Resource) → Set where
  stay : ∀ {x y} → x ≡ y → Adjacent N x y
  step : ∀ (m : N .Transition) → Adjacent N (N .inn m) (N .out m)

record Train (N : Infra) : Set₁ where
  field
    position   : ℕ → N .Resource
    continuous : ∀ n → Adjacent N (position n) (position (suc n))

open Train

Pairwise-consistent : ∀ {N : Infra} → Train N → Train N → ℕ → Set
Pairwise-consistent t₁ t₂ n = t₁ .position n ≢ t₂ .position n

pattern f0 = fzero
pattern f1 = fsuc fzero
pattern f2 = fsuc (fsuc fzero)
pattern f3 = fsuc (fsuc (fsuc fzero))

LoopStation : Set
LoopStation = Fin 4

LoopTrack : Set
LoopTrack = Fin 4

srcL : LoopTrack → LoopStation
srcL f0 = f0
srcL f1 = f1
srcL f2 = f2
srcL f3 = f3

dstL : LoopTrack → LoopStation
dstL f0 = f1
dstL f1 = f2
dstL f2 = f3
dstL f3 = f0

nextTrack : LoopTrack → LoopTrack
nextTrack f0 = f1
nextTrack f1 = f2
nextTrack f2 = f3
nextTrack f3 = f0

LoopResource : Set
LoopResource = LoopStation ⊎ LoopTrack

data LoopMove : Set where
  depart : LoopTrack → LoopMove
  arrive : LoopTrack → LoopMove
  pass   : LoopTrack → LoopMove

innL : LoopMove → LoopResource
innL (depart e) = inj₁ (srcL e)
innL (arrive e) = inj₂ e
innL (pass   e) = inj₂ e

outL : LoopMove → LoopResource
outL (depart e) = inj₂ e
outL (arrive e) = inj₁ (dstL e)
outL (pass   e) = inj₂ (nextTrack e)

loopInfra : Infra
loopInfra = record
  { Resource   = LoopResource
  ; Transition = LoopMove
  ; inn        = innL
  ; out        = outL
  }

orbitFrom : LoopTrack → ℕ → LoopTrack
orbitFrom t0 zero    = t0
orbitFrom t0 (suc n) = nextTrack (orbitFrom t0 n)

train₀ : Train loopInfra
train₀ = record
  { position   = λ n → inj₂ (orbitFrom f0 n)
  ; continuous = λ n → step (pass (orbitFrom f0 n))
  }

train₁ : Train loopInfra
train₁ = record
  { position   = λ n → inj₂ (orbitFrom f2 n)
  ; continuous = λ n → step (pass (orbitFrom f2 n))
  }

-- Proof: Train 0 and Train 1 are never on the same resource

nextTrack-inj : ∀ {x y : LoopTrack} → nextTrack x ≡ nextTrack y → x ≡ y
nextTrack-inj {f0} {f0} _ = refl
nextTrack-inj {f0} {f1} ()
nextTrack-inj {f0} {f2} ()
nextTrack-inj {f0} {f3} ()

nextTrack-inj {f1} {f0} ()
nextTrack-inj {f1} {f1} _ = refl
nextTrack-inj {f1} {f2} ()
nextTrack-inj {f1} {f3} ()

nextTrack-inj {f2} {f0} ()
nextTrack-inj {f2} {f1} ()
nextTrack-inj {f2} {f2} _ = refl
nextTrack-inj {f2} {f3} ()

nextTrack-inj {f3} {f0} ()
nextTrack-inj {f3} {f1} ()
nextTrack-inj {f3} {f2} ()
nextTrack-inj {f3} {f3} _ = refl

-- TO RESOLVE THE META...

f0t : Fin 4
f0t = fzero {n = 3}

f1t : Fin 4
f1t = fsuc (fzero {n = 2})

f2t : Fin 4
f2t = fsuc (fsuc (fzero {n = 1}))

f3t : Fin 4
f3t = fsuc (fsuc (fsuc (fzero {n = 0})))

f0≢f2 : f0t ≢ f2t
f0≢f2 ()

orbitFrom-inj :
  (n : ℕ) →
  ∀ {x y : LoopTrack} →
  orbitFrom x n ≡ orbitFrom y n → x ≡ y
orbitFrom-inj zero    eq = eq
orbitFrom-inj (suc n) eq = orbitFrom-inj n (nextTrack-inj eq)

orbitFrom-offset2≢ : (n : ℕ) → orbitFrom f0t n ≢ orbitFrom f2t n
orbitFrom-offset2≢ n eq = f0≢f2 (orbitFrom-inj n eq)

inj₂L : LoopTrack → LoopResource
inj₂L = inj₂ {A = LoopStation} {B = LoopTrack}

inj₂-injective-Loop : ∀ {x y : LoopTrack} → inj₂L x ≡ inj₂L y → x ≡ y
inj₂-injective-Loop refl = refl

pairwiseLoop : (n : ℕ) → Pairwise-consistent train₀ train₁ n
pairwiseLoop n eq =
  orbitFrom-offset2≢ n (inj₂-injective-Loop eq)



