```agda
open import Data.Sum
open import Data.Nat
open import Data.Fin
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong)
```

We first define what is the infrastructure for a rail system:
  - A set `Station` of stations.
  - A set `Track` of directed track segments.
  - Two functions:
    - `src : Track → Station` — where a track starts.
    - `dst : Track → Station` — where a track ends.

This would make a graph, and the graph can always be refined by adding stations on edges.

```agda
module RailSystem where

record Infra : Set₁ where
  field
    Station : Set
    Track : Set

    -- originally I was using Track A B (A, B are stations)
    -- but that did not work because
    -- (1) its constructor is not straightforward: 
    --     if we just use mktrack a b for all a, b 
    --     then that implies every two stations have a track between them
    -- (2) makes stating properties harder since we need to get the stations
    --     out from type parameters

    src : Track → Station
    dst : Track → Station

open Infra
```

For trains, they cannot teleport. Therefore, between time ticks they can only move
between `adjacent` posiitons. We define what is `adjacent`:

(1) the train stayed on the same station/track
(2) the train moved from a track to its dst station
(3) the train moved from a station to a track that originates from that station
(4) the train move from a track to another track connected via a station

```agda
data Adjacent (N : Infra) : (x y : N .Station ⊎ N .Track) → Set₁ where
  -- if two stations are the same station, they are adjacent
  station-station : ∀ {x y} → x ≡ y → Adjacent N (inj₁ x) (inj₁ y)
  -- if given a station and a track, the station is the source of the given track, they are adjacent
  station-track : ∀ {x e} → x ≡ N .src e → Adjacent N (inj₁ x) (inj₂ e)
  -- if given a station and a track, the station is the destiny of the given track, they are adjacent
  track-station : ∀ {e y} → N .dst e ≡ y → Adjacent N (inj₂ e) (inj₁ y)
  -- if given two tracks and they are connected via a station, they are adjacent
  -- (a train can move pass a station without stopping)
  track-track : ∀ {e₁ e₂} → N .dst e₁ ≡ N .src e₂ → Adjacent N (inj₂ e₁) (inj₂ e₂)
  -- a track is adjacent to itself
  track-track-id : ∀ {e₁ e₂} → e₁ ≡ e₂ → Adjacent N (inj₂ e₁) (inj₂ e₂)
```

A train is just a function from time ticks `ℕ` to positions (stations ⊎ tracks),
and it must satisfy the continuity condition (i.e. can only move between adjacent
locations between time ticks)

```agda
record Train (N : Infra) : Set₁ where
  field
    position : ℕ → N .Station ⊎ N .Track
    continuous : ∀ (n : ℕ) → Adjacent N (position n) (position (suc n))
open Train
```

Now we have physically possible trains, we can model their interactions.
Let's say we do not want to have two trains on the same track at once.
We define what is `consistent` for two trains to co-exist in the system:

(1) & (2): if one train is in a station, we are fine
(3): if two trains are both on tracks, they must not be on the same track

```agda
data Pairwise-consistent (N : Infra) (t₁ t₂ : Train N) (n : ℕ) : Set₁ where
  stationl : ∀ {s} → t₁ .position n ≡ inj₁ s → Pairwise-consistent N t₁ t₂ n
  stationr : ∀ {s} → t₂ .position n ≡ inj₂ s → Pairwise-consistent N t₁ t₂ n
  both-tracks
    : (e₁ : N .Track) (e₂ : N .Track)
    → t₁ .position n ≡ inj₂ e₁
    → t₂ .position n ≡ inj₂ e₂
    → e₁ ≢ e₂
    → Pairwise-consistent N t₁ t₂ n
```

Now we can define a Network (multiple trains running on an infra).
It is going to have some physically possible trains, and 
the property that all those trains can co-exist with each other.

```agda
record Network (N : Infra) : Set₁ where
  open Infra N
  field
    num-trains : ℕ
    trains : Fin num-trains → Train N
    consistent
      : ∀ (i j : Fin num-trains)
      → i ≢ j
      → ∀ n → Pairwise-consistent N (trains i) (trains j) n

```

Example time!

```agda
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin using (Fin ; zero ; suc)
```

Let's say we have 4 stations and 4 tracks:

```c
0 ------ 0 ------> 1
^                  | 
|                  1
3                  |
|                  |
3 <----- 2 ------- 2 
```

```agda
-- patterns for Fin 4
pattern f0 = zero
pattern f1 = suc zero
pattern f2 = suc (suc zero)
pattern f3 = suc (suc (suc zero))

-- 4 stations, 4 tracks in a directed loop:
--  track 0 : 0 → 1
--  track 1 : 1 → 2
--  track 2 : 2 → 3
--  track 3 : 3 → 0
loopInfra : Infra
loopInfra = record
  { Station = Fin 4
  ; Track   = Fin 4
  ; src     = λ { f0 → f0
                ; f1 → f1
                ; f2 → f2
                ; f3 → f3
                }
  ; dst     = λ { f0 → f1
                ; f1 → f2
                ; f2 → f3
                ; f3 → f0
                }
  }

LoopStation : Set
LoopStation = Infra.Station loopInfra

LoopTrack : Set
LoopTrack = Infra.Track loopInfra

srcL : LoopTrack → LoopStation
srcL = Infra.src loopInfra

dstL : LoopTrack → LoopStation
dstL = Infra.dst loopInfra
```

The movement pattern would just be trains running in loops!

```agda
-- next track on the loop
nextTrack : LoopTrack → LoopTrack
nextTrack f0 = f1
nextTrack f1 = f2
nextTrack f2 = f3
nextTrack f3 = f0

-- dst t = src (nextTrack t)
loopAdj : ∀ t → dstL t ≡ srcL (nextTrack t)
loopAdj f0 = refl   -- 1 = 1
loopAdj f1 = refl   -- 2 = 2
loopAdj f2 = refl   -- 3 = 3
loopAdj f3 = refl   -- 0 = 0

-- orbit starting from a given track, stepping with nextTrack
orbitFrom : LoopTrack → ℕ → LoopTrack
orbitFrom t0 zero    = t0
orbitFrom t0 (suc n) = nextTrack (orbitFrom t0 n)

-- Train 0: runs forever around the loop starting at track 0
train₀ : Train loopInfra
train₀ = record
  { position   = λ n → inj₂ (orbitFrom f0 n)
  ; continuous = λ n → track-track (loopAdj (orbitFrom f0 n))
  }

-- Train 1: runs forever around the loop starting at track 2
train₁ : Train loopInfra
train₁ = record
  { position   = λ n → inj₂ (orbitFrom f2 n)
  ; continuous = λ n → track-track (loopAdj (orbitFrom f2 n))
  }

-- Network with 2 trains on that loop

trainsLoop : Fin 2 → Train loopInfra
trainsLoop zero      = train₀
trainsLoop (suc zero) = train₁

loopNetwork : Network loopInfra
loopNetwork = record
  { num-trains = 2
  ; trains     = trainsLoop
  ; consistent = consistent'
  }
  where
    consistent'
      : ∀ (i j : Fin 2)
      → i ≢ j
      → ∀ n → Pairwise-consistent loopInfra (trainsLoop i) (trainsLoop j) n
    consistent' zero zero i≢j n = ⊥-elim (i≢j refl)
    consistent' (suc zero) (suc zero) i≢j n = ⊥-elim (i≢j refl)

    consistent' zero (suc zero) _ n =
      stationr refl

    consistent' (suc zero) zero _ n =
      stationr refl
```