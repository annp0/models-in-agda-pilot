-- a simple loop with 4 stations and 4 tracks
-- and two trains traveling around this circular loop

module LoopExample where

open import RailSystem
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Fin using (Fin) renaming (zero to fzero ; suc to fsuc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_ ; refl)


pattern f0 = fzero
pattern f1 = fsuc fzero
pattern f2 = fsuc (fsuc fzero)
pattern f3 = fsuc (fsuc (fsuc fzero))

-- 4 stations arranged in a loop
LoopStation : Set
LoopStation = Fin 4

-- 4 tracks connecting the stations in sequence
LoopTrack : Set
LoopTrack = Fin 4

-- source station of each track
-- track i connects station i to station (i+1) mod 4
srcL : LoopTrack → LoopStation
srcL f0 = f0
srcL f1 = f1
srcL f2 = f2
srcL f3 = f3

-- destination station of each track
dstL : LoopTrack → LoopStation
dstL f0 = f1
dstL f1 = f2
dstL f2 = f3
dstL f3 = f0

-- next track in the loop (clockwise)
nextTrack : LoopTrack → LoopTrack
nextTrack f0 = f1
nextTrack f1 = f2
nextTrack f2 = f3
nextTrack f3 = f0

-- resource in the loop is either a station or a track segment
LoopResource : Set
LoopResource = LoopStation ⊎ LoopTrack

-- Possible moves in the loop network:
--   depart: leave a station and enter the associated track
--   arrive: exit a track and enter the destination station
--   pass: move from one track to the next without stopping at the station
data LoopMove : Set where
  depart : LoopTrack → LoopMove  -- Depart station onto track
  arrive : LoopTrack → LoopMove  -- Arrive at station from track
  pass   : LoopTrack → LoopMove  -- Pass through without stopping

-- source resource for each type of move
innL : LoopMove → LoopResource
innL (depart e) = inj₁ (srcL e)  -- Departing from source station
innL (arrive e) = inj₂ e          -- Arriving from the track
innL (pass   e) = inj₂ e          -- Passing through from current track

-- destination resource for each type of move
outL : LoopMove → LoopResource
outL (depart e) = inj₂ e               -- Depart onto track
outL (arrive e) = inj₁ (dstL e)        -- Arrive at destination station
outL (pass   e) = inj₂ (nextTrack e)   -- Pass to next track

-- | The complete loop infrastructure
loopInfra : Infra
loopInfra = record
  { Resource   = LoopResource
  ; Transition = LoopMove
  ; inn        = innL
  ; out        = outL
  }

-- Train Definitions

-- Compute which track a train is on after n steps, starting from track t0
-- This models a train continuously circling the loop
orbitFrom : LoopTrack → ℕ → LoopTrack
orbitFrom t0 zero    = t0
orbitFrom t0 (suc n) = nextTrack (orbitFrom t0 n)

-- Train 0: starts on track 0 and continuously circles the loop
train₀ : Train loopInfra
train₀ = record
  { position   = λ n → inj₂ (orbitFrom f0 n)     -- Always on a track
  ; continuous = λ n → step (pass (orbitFrom f0 n))  -- Pass to next track each step
  }

-- Train 1: starts on track 2 and circles the loop
-- This train follows the same pattern as train₀ but offset by 2 positions
train₁ : Train loopInfra
train₁ = record
  { position   = λ n → inj₂ (orbitFrom f2 n)
  ; continuous = λ n → step (pass (orbitFrom f2 n))
  }


-- Safety Proof

-- 1. Proof that nextTrack is injective (one-to-one)
-- This is needed to show that if two orbits coincide at some point,
-- they must have started at the same track

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

f0t : Fin 4
f0t = fzero {n = 3}

f1t : Fin 4
f1t = fsuc (fzero {n = 2})

f2t : Fin 4
f2t = fsuc (fsuc (fzero {n = 1}))

f3t : Fin 4
f3t = fsuc (fsuc (fsuc (fzero {n = 0})))

-- | Proof that f0 and f2 are distinct
f0≢f2 : f0t ≢ f2t
f0≢f2 ()

-- 2. If two orbits are equal at time n, they must have started from the same track
orbitFrom-inj :
  (n : ℕ) →
  ∀ {x y : LoopTrack} →
  orbitFrom x n ≡ orbitFrom y n → x ≡ y
orbitFrom-inj zero    eq = eq
orbitFrom-inj (suc n) eq = orbitFrom-inj n (nextTrack-inj eq)

-- since f0 ≠ f2, and orbitFrom is injective, the orbits are always different
orbitFrom-offset2≢ : (n : ℕ) → orbitFrom f0t n ≢ orbitFrom f2t n
orbitFrom-offset2≢ n eq = f0≢f2 (orbitFrom-inj n eq)

inj₂L : LoopTrack → LoopResource
inj₂L = inj₂ {A = LoopStation} {B = LoopTrack}

-- inj₂ is injective for LoopResource
inj₂-injective-Loop : ∀ {x y : LoopTrack} → inj₂L x ≡ inj₂L y → x ≡ y
inj₂-injective-Loop refl = refl

-- main safety theorem
pairwiseLoop : (n : ℕ) → Pairwise-consistent train₀ train₁ n
pairwiseLoop n eq =
  orbitFrom-offset2≢ n (inj₂-injective-Loop eq)