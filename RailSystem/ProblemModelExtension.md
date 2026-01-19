We now take the problem space model (`RailSystem`) as the starting point: an `Infra` of Resources and Transitions, an `Adjacent` relation (stay/step), and trains as time-indexed positions with a continuity proof. Now we try to refine that core by adding structure and properties, or by replacing one permissive clause with a stronger one, while keeping the original shape recognisable.

### 1. Refinement by Occupancy Policy

Right now, the model's safety constraint is essentially: trains must not coincide at time `n` (`Pairwise-consistent`).

A first refinement is to separate "where a train is" from "what it occupies".

We can introduce an occupancy footprint map `occ: Train -> Time -> Resources`

so that exclusivity is stated as:

* `Disjoint (occ train0 t) (occ train1 t)`

This is strictly richer than `pos₁ n ≢ pos₂ n`. Now we can have

* rail: a train on a track occupies the track segment (and maybe also a safety buffer)
* stations: may allow multiple trains to co-exist in a station (platform model), or forbid it (single-bay station)

Once occupancy is explicit, we can parameterise a "policy":

* rail policy: exclusive on tracks, maybe exclusive on stations, maybe block buffers
* road policy: non-exclusive occupancy but "separation distance" constraint
* air/sea policy: occupancy becomes a 3D/continuous safety envelope

### 2. Refinement of Adjacency

Our current approach for adjacency is basically "stutter or take one transition". We can do at least three clean refinements here:

#### 2.1 Multi step macro transitions

Sometimes we want to treat a whole manoeuvre as one step (enter station -> dwell -> depart). We can refine by introducing:

* a richer `Transition` type whose constructors encode macro-moves
* keep primitive transitions but define a derived reachability `Adjacent⁺` for bounded/controlled multi-step moves

With this we can start expressing control logic without leaving the problem-space.

#### 2.2 Time-dependent adjacency

Real networks have signalling, closures, maintenance windows, etc. Refinement:

* `Adjacent : ℕ → Resource → Resource → Set`
  or
* `enabled : ℕ → Transition → Set` plus `step : enabled n m → Adjacent n (inn m) (out m)`

#### 2.3 Capacity-refined adjacency

Instead of boolean adjacency, we can make it resource-aware, where for example adjacency is allowed only if a capacity constraint holds (e.g., headway, block availability)

### 3. Refinement by Introducing "Segments" and "Stations" as Meta-Structures

Instead of one undifferentiated `Resource`, we can refine into:

* atomic occupancy units (track segments, platform segments, runway segments)
* meta resources (stations, yards, terminals) which correspond to sets of atomic units

Then trains still live on atomic units, but we can observe "which station am I in" as a derived predicate. Then we can define a "view" function:

* `stationOf : Resource → Maybe Station`
* `sectorOf : Resource → Sector` (airspace)
* `laneOf : Resource → Lane` (road)

This yields very natural invariants, like, if you're in sector S, your altitude band must be ...

### 4. Refinement by Intent and Plan

Right now a train is just a physically possible trajectory. A refinement we can do is to add normative structure.

For example, we can add a plan: `plan : ℕ → Pred Resource` (allowed corridor at time n) , then constrain: `position n ∈ plan n`.

We can also introduce a controller-issued "movement authority": `auth : Train → ℕ → Pred Transition` and refine continuity to require not just adjacency, but authorised adjacency.

This keeps the model physical, but now it reflects signalling/ATC/traffic management.

### 5. Refinement by Failure Modes and Partiality

The pure model assumes everything is total and perfect. A classic refinement (still problem-space) is to admit blocked transitions abd broken resources.

We can add partiality:

* `out : Transition → Maybe Resource`
* or `enabled : ℕ → Transition → Set` (simpler)

Then we can state invariants like "if blocked, trains must stutter or reroute".

### The Pattern

All of the above are the same move in different clothes:

* start with `Resource`, `Transition`, `Adjacent`, `Train`
* either add observers/attributes (occupancy footprints, geometry, views)
* or strengthen constraints (authorisation, time-dependent enabling, separation)
* without changing the fundamental idea: a train is a time-indexed occupation constrained locally at each tick

