module RailSystem where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Fin using (Fin) renaming (zero to fzero ; suc to fsuc)
open import Data.Empty using (⊥ ; ⊥-elim)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_ ; refl)

-- Infrastructure Model

-- Infrastructure consists of:
--  1. resources: locations that trains can occupy
--  2. transitions: atomic moves between resources
--  3. inn/out: source and destination of each transition

record Infra : Set₁ where
  field
    Resource    : Set -- locations/resources in the network
    Transition  : Set -- possible moves between resources
    inn         : Transition → Resource -- source resource of a transition
    out         : Transition → Resource -- destination resource of a transition

open Infra

-- two resources are adjacent if there exists a transition connecting them,
-- or if they are the same resource

data Adjacent (N : Infra) : (x y : N .Resource) → Set where
  stay : ∀ {x y} → x ≡ y → Adjacent N x y
  step : ∀ (m : N .Transition) → Adjacent N (N .inn m) (N .out m)

-- a train in a rail network is defined by:
--  position: its location at each discrete time step (ℕ represents time)
--  continuous: proof that it only moves to adjacent resources at each step

record Train (N : Infra) : Set₁ where
  field
    position   : ℕ → N .Resource
    continuous : ∀ n → Adjacent N (position n) (position (suc n))

open Train

-- Two trains are pairwise consistent at time n if they occupy different resources.
-- no two trains can occupy the same resource
--
-- For a system with multiple trains, we would need to prove this property holds
-- for all pairs at all times.
Pairwise-consistent : ∀ {N : Infra} → Train N → Train N → ℕ → Set
Pairwise-consistent t₁ t₂ n = t₁ .position n ≢ t₂ .position n