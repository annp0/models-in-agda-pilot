module RailSystemPaper where

-- Chapter 4: Graphs: Transport Nets, Sections 4.1–4.4
--  it distinguishes aggregate objects (EA, NA) from sets (ES, NS)
--  & introduces explicit UID sorts for many things
--  & defines "observers" on nodes/edges in terms of UID sets.
--  & defines Paths as alternating sequences of edge/node identifiers.

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Product using (_×_; Σ; Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Data.Nat using (ℕ; suc)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec)
open import Data.Unit using (⊤; tt)

-- The spec uses ES = E-set, NS = N-set, etc.
-- In Agda, we encode "set of A" as a predicate A → Set.


Pred : ∀ {ℓ} → Set ℓ → Set (lsuc ℓ)
Pred {ℓ} A = A → Set ℓ

_∈_ : ∀ {ℓ} {A : Set ℓ} → A → Pred A → Set ℓ
x ∈ S = S x

_⊆_ : ∀ {A : Set} → Pred A → Pred A → Set
S ⊆ T = ∀ x → x ∈ S → x ∈ T

-- 4.1
--
-- External qualities are the endurant sorts:
--   G  : graphs (transport nets)
--   EA : edge aggregate (an "aggregate object", not a set)
--   NA : node aggregate (same idea)
--   ES : set of edges
--   NS : set of nodes
--   E  : edges (atomic)
--   N  : nodes (atomic)
--
--   obs EA : G → ES   (from a graph, observe the set of edges)
--   obs ES : EA → ES  (from an edge-aggregate object, observe edge-set)

postulate
  G  : Set        -- Graph sort
  E  : Set        -- Edge sort
  N  : Set        -- Node sort

postulate
  EA : Set        -- Edge-aggregate object sort
  NA : Set        -- Node-aggregate object sort

-- 19. ES = E-set, 20. NS = N-set
ES : Set₁
ES = Pred E

NS : Set₁
NS = Pred N

-- let's say a small railway system
-- Station A ----track1---- Station B ----track2---- Station C
-- g : G is the entire graph representing the railway network (the network itself)
-- EA is a data structure storing edge information (database table etc.)
--     (edge-aggregate object)
-- track1, track2: E, individual tracks (atomic edges)

-- From the graph, observe which tracks are part of the network
-- ea : ES
-- ea = obsEA g
-- Result: ea(track1) = ⊤ (track1 is in the network)
--         ea(track2) = ⊤ (track2 is in the network)
--         ea(track99) = ⊥ (track99 is not in this network)

-- From the EA, observe which tracks are registered
-- es : ES  
-- es = obsES eaAgg
-- Result: es(track1) = ⊤ (track1 is registered)
--         es(track2) = ⊤ (track2 is registered)
--         es(track99) = ⊥ (track99 is not registered)

-- if ea and es match: the graph's topology and the edge registry aggregate

-- if ea knows track3 but es does not, then this could represent a track that is not built in the database
-- or planned track v. actual tracks

-- if es knows track3 but ea does not, then this could represent a track that is 
-- currently undermaintance (exist in registry, but not avaliable in topology)

-- this should be for seperation of concern

-- 17. 18.
postulate
  obsEA : G → ES
  obsNA : G → NS

-- 19. 20.
postulate
  obsES : EA → ES
  obsNS : NA → NS

-- 23.
-- Source writes: P = G|EA|NA|ES|NS|N|E.

-- P is the "part" sort
-- a sum type that represents all possible kinds of parts
-- (a graph, individual edge, node, ea/es)

data P : Set where
  pG  : G  → P
  pEA : EA → P
  pNA : NA → P
  pE  : E  → P
  pN  : N  → P

P-set : Set₁
P-set = Pred P

-- for example:
-- ├─ pG myNetwork              -- The whole network graph
-- ├─ pEA trackDatabase         -- The track database/registry
-- ├─ pNA stationDatabase       -- The station database/registry
-- ├─ pE track1                 -- Individual track between A-B
-- ├─ pE track2                 -- Individual track between B-C
-- ├─ pN stationA               -- Station A
-- ├─ pN stationB               -- Station B
-- └─ pN stationC               -- Station C

-- 4.1.1

postulate
  g      : G -- a specific graph instance
  eaAgg  : EA -- a specific ea
  naAgg  : NA -- a specific na

ea : ES -- extracting the edge set frm the graph
ea = obsEA g

na : NS -- node set
na = obsNA g

es : ES
es = obsES eaAgg

ns : NS
ns = obsNS naAgg

-- 28. σ : P-set = {g}∪{eaAgg}∪{naAgg}∪es∪ns
-- σ is the state of the railway system
-- (which parts currently exist in the system)
-- e.g.
-- σ (pG myNetwork) = ⊤     The network graph exists
-- σ (pG otherNetwork) = ⊥  Other networks don't exist here
-- σ (pEA trackDatabase) = ⊤       The track database exists
-- σ (pNA stationDatabase) = ⊤        The station database exists 
-- σ (pE track1) = ⊤                  track1 is in es
-- σ (pE track2) = ⊤                  track2 is in es
-- σ (pE track99) = ⊥                 track99 is NOT in es
-- σ (pN stationA) = ⊤         stationA is in ns
-- σ (pN stationB) = ⊤         stationB is in ns
-- σ (pN stationC) = ⊤         stationC is in ns
-- σ (pN stationZ) = ⊥         stationZ is NOT in ns


σ : P-set
σ (pG  g′)  = g′ ≡ g
σ (pEA a)   = a ≡ eaAgg
σ (pNA a)   = a ≡ naAgg
σ (pE  e′)  = e′ ∈ es
σ (pN  n′)  = n′ ∈ ns


-- 4.2 Unique Identifiers
-- (identifier system for the railway netwrork)

-- GI = Graph Identifier (like Network-12345)
-- EAI = Edge-Aggregate Identifier (like TrackDB-001)
-- NAI = Node-Aggregate Identifier (like StationDB-001)
-- ESI = Edge-Set Identifier (like EdgeCollection-99)
-- NSI = Node-Set Identifier (like NodeCollection-88)
-- EI = Edge Identifier (like Track-A1, Track-B2)
-- NI = Node Identifier (like Station-A, Station-B)

postulate
  GI  EAI  NAI  ESI  NSI  EI  NI : Set

data PI : Set where
  gi  : GI  → PI
  eai : EAI → PI
  nai : NAI → PI
  esi : ESI → PI
  nsi : NSI → PI
  ei  : EI  → PI
  ni  : NI  → PI

PI-set : Set₁
PI-set = Pred PI

-- 30–33 uid observers:
-- for example:
-- track1 : E                      -- The physical track A→B
-- uidE track1 = "Track-A1"        -- Its identifier
-- stationA : N                    -- The physical station A
-- uidN stationA = "Station-A"     -- Its identifier
-- myNetwork : G                   -- The network graph
-- uidG myNetwork = "Network-12345" -- Its identifier

postulate
  uidG  : G  → GI      -- Extract the ID from a graph
  uidEA : EA → EAI     -- Extract the ID from an edge-aggregate
  uidNA : NA → NAI     -- Extract the ID from a node-aggregate
  uidES : EA → ESI     -- Extract edge-set ID from aggregate
  uidNS : NA → NSI     -- Extract node-set ID from aggregate
  uidE  : E  → EI      -- Extract the ID from an edge
  uidN  : N  → NI      -- Extract the ID from a node

-- "global" identifiers (spec 35–39)
-- the name of the graph/EA/NA... for our SPECIFIC model
-- for example
-- gi′ = "Network-12345"           -- Our network's ID
-- eauis = "TrackDB-001"          -- Our track database's ID
-- nauis = "StationDB-001"        -- Our station database's ID
-- esuis = "EdgeCollection-99"    -- Edge collection ID
-- nsuis = "NodeCollection-88"    -- Node collection ID
gi′ : GI
gi′ = uidG g

eauis : EAI
eauis = uidEA eaAgg

nauis : NAI
nauis = uidNA naAgg

esuis : ESI
esuis = uidES eaAgg

nsuis : NSI
nsuis = uidNS naAgg

-- 38. euis = {uidE(e) | e ∈ es}
-- 39. nuis = {uidN(n) | n ∈ ns}
--
-- As sets-of-identifiers, encode as predicates over EI / NI.
-- basically
-- Euis "Track-A1" = ⊤            -- Track-A1's ID is in the system
-- Euis "Track-B2" = ⊤            -- Track-B2's ID is in the system
-- Euis "Track-Z99" = ⊥           -- Track-Z99's ID is NOT in the system
Euis : Pred EI
Euis i = Σ[ e ∈ E ] (e ∈ es × uidE e ≡ i)

Nuis : Pred NI
Nuis i = Σ[ n ∈ N ] (n ∈ ns × uidN n ≡ i)

-- 40. σuis = {gi}∪{eauis}∪{nauis}∪{esuis}∪{nsuis}∪euis∪nuis

σuis : PI-set
σuis (gi  x) = x ≡ gi′         -- Only THE graph's ID is in state
σuis (eai x) = x ≡ eauis       -- Only THE edge-agg ID is in state
σuis (nai x) = x ≡ nauis       -- Only THE node-agg ID is in state
σuis (esi x) = x ≡ esuis       -- Only THE edge-set ID is in state
σuis (nsi x) = x ≡ nsuis       -- Only THE node-set ID is in state
σuis (ei  x) = x ∈ Euis        -- Edge ID x is in state if in Euis
σuis (ni  x) = x ∈ Nuis        -- Node ID x is in state if in Nuis

-- 41. Uniqueness axiom:
--   card σ = card σuis
--
-- They are comparing cardinality of "part state" vs "identifier state".
-- We do not have a finiteness model, so postulate card.
postulate
  cardP  : P-set  → ℕ
  cardPI : PI-set → ℕ
  Uniqueness-of-Part-Identification : cardP σ ≡ cardPI σuis

-- 4.3 Mereology (Mereology = the study of "part-whole" relationships. 
-- here it describes which tracks connect to which stations)
--
-- Spec:
-- 42. NM = EI-set, nonempty
-- 43. EM = NI-set, of size 2
-- mereo N: N → NM
-- mereo E: E → EM
-- wellformedness: referenced IDs come from the graph.

NM : Set₁
NM = Pred EI -- -- Node Mereology: set of Edge IDs

EM : Set₁
EM = Pred NI -- -- Node Mereology: set of Edge IDs

-- Cardinality constraints are axioms in the spec.
postulate
  cardEI : NM → ℕ
  cardNI : EM → ℕ

postulate
  mereoN : N → NM    -- Given a station, return its incident tracks
  mereoE : E → EM    -- Given a track, return its endpoint stations

-- stationA : N
-- mereoN stationA = { "Track-A1" }         -- Station A touches track1
-- mereoN stationA "Track-A1" = ⊤       (track1 is incident to stationA)
-- mereoN stationA "Track-B2" = ⊥       (track2 is NOT incident to stationA)

-- stationB : N
-- mereoN stationB = { "Track-A1", "Track-B2" }  -- Station B touches both tracks
-- mereoN stationB "Track-A1" = ⊤       (track1 touches stationB)
-- mereoN stationB "Track-B2" = ⊤       (track2 touches stationB)

-- stationC : N
-- mereoN stationC = { "Track-B2" }         -- Station C touches track2
-- mereoN stationC "Track-B2" = ⊤       (track2 touches stationC)

AllEI : Pred EI
AllEI i = Σ[ e ∈ E ] (e ∈ es × uidE e ≡ i)
-- "Edge ID i exists in the system"

AllNI : Pred NI
AllNI i = Σ[ n ∈ N ] (n ∈ ns × uidN n ≡ i)
-- "Node ID i exists in the system"

-- 44. mereoN(n) ⊆ es-IDs
-- 45. mereoE(e) ⊆ ns-IDs
postulate
  Graph-Mereology-Wellformedness-44 : ∀ n → mereoN n ⊆ AllEI
    -- All track IDs referenced by a station actually exist in the graph
  Graph-Mereology-Wellformedness-45 : ∀ e → mereoE e ⊆ AllNI
    -- All station IDs referenced by a track actually exist in the graph


-- 4.4 Paths of a Graph
--
-- Spec:
-- 46. Path = (EI|NI)*
-- plus a large wellformedness axiom requiring:
--  - alternating EI/NI
--  - IDs belong to graph
--  - neighbour constraints follow mereology


-- a path is a (possibly empty) sequence of edge or node identifiers

UI : Set
UI = EI ⊎ NI

Path : Set
Path = List UI

-- alternation between node-id and edge-id in a path
data AdjUI : UI → UI → Set where
  ni-ei : ∀ {ni′ ei′} → AdjUI (inj₂ ni′) (inj₁ ei′)
  ei-ni : ∀ {ei′ ni′} → AdjUI (inj₁ ei′) (inj₂ ni′)

-- Node ID ni′ exists in the system
NSuis : Pred NI
NSuis ni′ = Σ[ n ∈ N ] (n ∈ ns × uidN n ≡ ni′)

-- Similar
ESuis : Pred EI
ESuis ei′ = Σ[ e ∈ E ] (e ∈ es × uidE e ≡ ei′)

-- Retrieval functions (spec 47): given an identifier, retrieve the entity.
postulate
  retrNode : NI → N
  retrEdge : EI → E

-- Correctness: retrieved item is in the global set and has that UID.
postulate
  retrNode-correct :
    ∀ (ni′ : NI) →
      let n = retrNode ni′ in (n ∈ ns) × (uidN n ≡ ni′)

  retrEdge-correct :
    ∀ (ei′ : EI) →
      let e = retrEdge ei′ in (e ∈ es) × (uidE e ≡ ei′)

-- Wellformed neighbour constraint:
-- If (NI then EI) => EI is in mereoN(retrNode NI)
-- If (EI then NI) => NI is in mereoE(retrEdge EI)
WFStep : UI → UI → Set
WFStep (inj₂ ni′) (inj₁ ei′) =
  (ni′ ∈ NSuis) × (ei′ ∈ ESuis) × (ei′ ∈ mereoN (retrNode ni′))
WFStep (inj₁ ei′) (inj₂ ni′) =
  (ei′ ∈ ESuis) × (ni′ ∈ NSuis) × (ni′ ∈ mereoE (retrEdge ei′))
WFStep _ _ = ⊥

-- Inductive wellformedness predicate over finite paths.
-- This corresponds to the ∀ {i,i+1} ⊆ inds path ⇒ ... constraint in the spec.
data WellformedPath : Path → Set where
  wf[]  : WellformedPath []
  wf1   : ∀ {u} → WellformedPath (u ∷ [])
  wf∷∷  : ∀ {u v rest}
        → AdjUI u v
        → WFStep u v
        → WellformedPath (v ∷ rest)
        → WellformedPath (u ∷ v ∷ rest)

postulate
  Wellformed-Paths-46 : ∀ (p : Path) → Set

-- 48–52 paths : G → Path-infset
-- A set of paths is a predicate over paths
Path-set : Set₁
Path-set = Pred Path

-- Paths observer - given a graph, return all valid paths in it
postulate
  paths : G → Path-set

pathsGlobal : Path-set
pathsGlobal = paths g


-- 53 reverse paths theorem
--
-- They define rev path and claim:
--   ∀ g, p ∈ paths(g) ⇒ rev(p) ∈ paths(g)
-- We use list reverse

revPath : Path → Path
revPath = Data.List.reverse

postulate
  All-finite-paths-have-finite-reverse-paths-53 :
    ∀ (g′ : G) (p : Path) → p ∈ paths g′ → revPath p ∈ paths g′
