module RailSystemPaper where

------------------------------------------------------------------------
-- Chapter 4: "Graphs: Transport Nets", Sections 4.1–4.4
--
-- The source uses a classical RSL ish style:
--   - It distinguishes aggregate objects (EA, NA) from sets (ES, NS)
--   - It introduces explicit UID sorts for many things
--   - It defines "observers" on nodes/edges in terms of UID sets.
--   - It defines Paths as alternating sequences of edge/node identifiers.
--
-- In Agda, we make a few representation choices:
--   (A) We represent mathematical sets as predicates: Pred A = A → Set.
--       This is the standard Agda encoding.
--   (B) Where the spec speaks about cardinalities (card), we postulate them
--       because the spec itself does not give a constructive finiteness model.
--   (C) Some global state lines in the spec are inconsistent (EA vs ES),
--       so we keep both levels (EA/NA aggregates and ES/NS sets) explicit,
--       and use postulates for the missing glue values.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Product using (_×_; Σ; Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Data.Nat using (ℕ; suc)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec)
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- The spec uses ES = E-set, NS = N-set, etc.
-- In Agda, we encode "set of A" as a predicate A → Set.
------------------------------------------------------------------------

Pred : ∀ {ℓ} → Set ℓ → Set (lsuc ℓ)
Pred {ℓ} A = A → Set ℓ

_∈_ : ∀ {ℓ} {A : Set ℓ} → A → Pred A → Set ℓ
x ∈ S = S x

_⊆_ : ∀ {A : Set} → Pred A → Pred A → Set
S ⊆ T = ∀ x → x ∈ S → x ∈ T

------------------------------------------------------------------------
-- 4.1 The Endurant Sorts and Observers
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
--
------------------------------------------------------------------------

postulate
  G  : Set        -- Graph sort
  E  : Set        -- Edge sort (atomic)
  N  : Set        -- Node sort (atomic)

postulate
  EA : Set        -- Edge-aggregate object sort (endurant)
  NA : Set        -- Node-aggregate object sort (endurant)

-- 19. ES = E-set, 20. NS = N-set
ES : Set₁
ES = Pred E

NS : Set₁
NS = Pred N


-- 17. obs EA: G → ES
-- 18. obs NA: G → NS
postulate
  obsEA : G → ES
  obsNA : G → NS

-- 19. obs ES: EA → ES
-- 20. obs NS: NA → NS
postulate
  obsES : EA → ES
  obsNS : NA → NS

-- 23.
-- Source writes: P = G|EA|NA|ES|NS|N|E.
--
-- In Agda, we can only store values, not predicate-functions cleanly as
-- first-class "parts" without extra universe machinery. The spec's state σ
-- effectively includes g, the aggregate objects, and the elements of es/ns.
-- So we model P as the sum of: graph, aggregates, and atomic E/N.
data P : Set where
  pG  : G  → P
  pEA : EA → P
  pNA : NA → P
  pE  : E  → P
  pN  : N  → P

P-set : Set₁
P-set = Pred P

------------------------------------------------------------------------
-- 4.1.1 An Endurant State
--
------------------------------------------------------------------------

postulate
  g      : G
  eaAgg  : EA
  naAgg  : NA

ea : ES
ea = obsEA g

na : NS
na = obsNA g

es : ES
es = obsES eaAgg

ns : NS
ns = obsNS naAgg

-- 28. σ : P-set = {g}∪{eaAgg}∪{naAgg}∪es∪ns
-- Since es/ns are sets of atomic E/N, we include them by including their
-- members as pE/pN parts.
σ : P-set
σ (pG  g′)  = g′ ≡ g
σ (pEA a)   = a ≡ eaAgg
σ (pNA a)   = a ≡ naAgg
σ (pE  e′)  = e′ ∈ es
σ (pN  n′)  = n′ ∈ ns

------------------------------------------------------------------------
-- Internal qualities: unique identification, mereology, etc.
-- 4.2 Unique Identifiers
--
-- The spec introduces distinct UID sorts:
--   GI, EAI, NAI, ESI, NSI, EI, NI
-- and a sum PI of "part identifiers".
--
-- In Agda, we encode those as postulated type.
-- Then we define "global UID state" σuis as a predicate over PI.
------------------------------------------------------------------------

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
-- uid G : G→GI
-- uid EA: EA→EAI, uid NA: NA→NAI
-- uid ES: ES→ESI, uid NS: NS→NSI  (spec says ES/NS, but we keep it tied to EA/NA)
-- uid E : E→EI, uid N : N→NI
postulate
  uidG  : G  → GI
  uidEA : EA → EAI
  uidNA : NA → NAI
  uidES : EA → ESI 
  uidNS : NA → NSI
  uidE  : E  → EI
  uidN  : N  → NI

-- "global" identifiers (spec 35–39)
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
Euis : Pred EI
Euis i = Σ[ e ∈ E ] (e ∈ es × uidE e ≡ i)

Nuis : Pred NI
Nuis i = Σ[ n ∈ N ] (n ∈ ns × uidN n ≡ i)

-- 40. σuis = {gi}∪{eauis}∪{nauis}∪{esuis}∪{nsuis}∪euis∪nuis
σuis : PI-set
σuis (gi  x) = x ≡ gi′
σuis (eai x) = x ≡ eauis
σuis (nai x) = x ≡ nauis
σuis (esi x) = x ≡ esuis
σuis (nsi x) = x ≡ nsuis
σuis (ei  x) = x ∈ Euis
σuis (ni  x) = x ∈ Nuis

-- 41. Uniqueness axiom:
--   card σ = card σuis
--
-- They are comparing cardinality of "part state" vs "identifier state".
-- We do not have a finiteness model, so postulate card.
postulate
  cardP  : P-set  → ℕ
  cardPI : PI-set → ℕ
  Uniqueness-of-Part-Identification : cardP σ ≡ cardPI σuis

------------------------------------------------------------------------
-- 4.3 Mereology
--
-- Spec:
-- 42. NM = EI-set, nonempty
-- 43. EM = NI-set, of size 2
-- mereo N: N → NM
-- mereo E: E → EM
-- wellformedness: referenced IDs come from the graph.
--
-- Again, we encode identifier-sets as predicates.
------------------------------------------------------------------------

NM : Set₁
NM = Pred EI

EM : Set₁
EM = Pred NI

-- Cardinality constraints are axioms in the spec.
postulate
  cardEI : NM → ℕ
  cardNI : EM → ℕ

postulate
  mereoN : N → NM
  mereoE : E → EM

AllEI : Pred EI
AllEI i = Σ[ e ∈ E ] (e ∈ es × uidE e ≡ i)

AllNI : Pred NI
AllNI i = Σ[ n ∈ N ] (n ∈ ns × uidN n ≡ i)

-- 44. mereoN(n) ⊆ es-IDs
-- 45. mereoE(e) ⊆ ns-IDs
postulate
  Graph-Mereology-Wellformedness-44 : ∀ n → mereoN n ⊆ AllEI
  Graph-Mereology-Wellformedness-45 : ∀ e → mereoE e ⊆ AllNI

------------------------------------------------------------------------
-- 4.4 Paths of a Graph
--
-- Spec:
-- 46. Path = (EI|NI)*
-- plus a large wellformedness axiom requiring:
--  - alternating EI/NI
--  - IDs belong to graph
--  - neighbour constraints follow mereology
--
------------------------------------------------------------------------

UI : Set
UI = EI ⊎ NI

Path : Set
Path = List UI

-- alternation between node-id and edge-id in a path
data AdjUI : UI → UI → Set where
  ni-ei : ∀ {ni′ ei′} → AdjUI (inj₂ ni′) (inj₁ ei′)
  ei-ni : ∀ {ei′ ni′} → AdjUI (inj₁ ei′) (inj₂ ni′)

NSuis : Pred NI
NSuis ni′ = Σ[ n ∈ N ] (n ∈ ns × uidN n ≡ ni′)

ESuis : Pred EI
ESuis ei′ = Σ[ e ∈ E ] (e ∈ es × uidE e ≡ ei′)

-- Retrieval functions (spec 47): given an identifier, retrieve the entity.
-- The spec gives them as pre/post conditions
-- We model that by postulating the retrieval functions plus correctness.
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

-- If you want to mirror the spec literally as an axiom:
-- “All paths in paths(g) satisfy wellformedness”
-- you can keep WellformedPath and later relate it to paths.
postulate
  Wellformed-Paths-46 : ∀ (p : Path) → Set
  -- Typically you’d set: Wellformed-Paths-46 p = WellformedPath p

------------------------------------------------------------------------
-- 48–52 paths : G → Path-infset
--
-- They say "possibly infinite set of paths", but paths themselves are finite
-- sequences (Path = (EI|NI)*). So "infinite" refers to the set being infinite.
--
-- In Agda, a “set of paths” is Pred Path.
------------------------------------------------------------------------

Path-set : Set₁
Path-set = Pred Path

postulate
  paths : G → Path-set

pathsGlobal : Path-set
pathsGlobal = paths g

------------------------------------------------------------------------
-- 53 reverse paths theorem
--
-- They define rev path and claim:
--   ∀ g, p ∈ paths(g) ⇒ rev(p) ∈ paths(g)
-- We use list reverse.
------------------------------------------------------------------------

revPath : Path → Path
revPath = Data.List.reverse

postulate
  All-finite-paths-have-finite-reverse-paths-53 :
    ∀ (g′ : G) (p : Path) → p ∈ paths g′ → revPath p ∈ paths g′
