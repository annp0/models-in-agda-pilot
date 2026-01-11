# Comparing the Two Models

We consider two related but distinct formal models of railway systems:

* Problem space (`RailSystem`): a physical model that directly represents trains moving through infrastructure. It focuses on resources (locations), transitions (moves), adjacency, and continuity constraints on time-indexed trajectories.

* Solution space (`RailSystemPaper`): a specification-oriented model that focuses on identifiers, aggregates, mereology, etc. It aligns more closely with how railway networks are represented, stored, and reasoned about in software systems.

Although both models describe the same underlying domain, they operate at different semantic levels and make different design commitments.

## Nodes vs. Resources

### Semantic role

In the solution space, nodes (`N`) are atomic endurant parts of a graph. Their role is defined relationally:

* Nodes belong to a graph via predicates (`NS`, `obsNA : G → NS`).
* Nodes are referenced indirectly through node identifiers (`NI`).
* A retrieval function (`retrNode : NI → N`) mediates access to the actual node.
* Global membership is tracked via identifier predicates (`NSuis`).

The emphasis is on identification & membership not direct usage.

In the problem space, resources (`Infra.Resource`) represent physical locations that trains may occupy. Resources are not identified indirectly and are not mediated by observers or retrieval:

* Trains occupy resources directly.
* Equality of resources (`_≡_`) is the primitive notion used for safety.
* There is no notion of identifiers, registries, or membership predicates.

Here, the emphasis is on physical occupancy and motion not representation.

### Implementation consequences

The solution model mirrors how railway data is typically handled in software: nodes are database entities with stable identifiers, global membership, and retrieval invariants.

The problem model intentionally avoids this layer. By working directly with denotations (resources), it keeps reasoning about occupancy, adjacency, and exclusivity minimal and local.

## Edges vs. Transitions

### Semantic role

In the solution space, edges (`E`) are undirected atomic connections in a graph:

* Each edge has a unique identifier (`EI`).
* Its endpoints are given by mereology (`mereoE : E → Pred NI`), yielding exactly two node identifiers.
* Orientation is not intrinsic; traversal direction emerges from how paths are constructed.

In the problem space, transitions (`Infra.Transition`) are primitive directed moves:

* Each transition has an explicit source and destination (`inn`, `out`).
* Directionality is built into the model.
* Transitions directly witness adjacency.

### Implementation consequences

The solution model encodes connectivity declaratively via identifier sets and axioms. Direction is imposed later, if needed, by path traversal rules.

The problem model encodes direction operationally. This aligns naturally with time-indexed motion, where movement is observed as a change from one resource to another.

## Mereology vs. Adjacency

### Semantic role

The solution space uses mereology to describe incidence relationships:

* `mereoN : N → Pred EI` gives the set of incident edge identifiers.
* `mereoE : E → Pred NI` gives the two endpoint node identifiers.
* Wellformedness axioms ensure all referenced identifiers belong to the current graph.

Adjacency is derived indirectly through these relations and enforced at the level of paths.

In the problem space, adjacency is a primitive relation:

* `Adjacent x y` directly witnesses that movement from `x` to `y` is allowed.
* This may be via stasis or via a transition with matching `inn`/`out`.

## Paths vs. Train Movement

### Semantic role

In the solution space, path are combinatorial objects:

* `Path = List (EI ⊎ NI)` is an alternating sequence of identifiers.
* Well-formedness (`WellformedPath`) enforces alternation, membership, and mereology constraints.
* Paths support reasoning about reachability, connectivity, and graph properties.

In the problem space, train behaviour is behavioural:

* A train is a function `position : ℕ → Resource`.
* A continuity proof ensures each step respects adjacency.

### Implementation consequences

Paths are suited for software-level reasoning (e.g. validating routes, computing reachability).

Trains are suited for physical reasoning (e.g. collision avoidance, mutual exclusion over time).

## Identifiers (UIDs)

### Semantic role

The solution space introduces a comprehensive UID discipline:

* Distinct identifier sorts (`GI`, `EI`, `NI`, etc.).
* A global part state (`σ`) and identifier state (`σuis`).
* A cardinality axiom (`cardP σ ≡ cardPI σuis`) tying entities to identifiers.
* Retrieval and correctness axioms ensuring consistency.

This reflects software concerns. The problem space has no identifiers and equality and inequality are defined directly on resources.

## Mapping the Solution Model to the Problem Model

The solution model can be projected into the problem model by *forgetting implementation artefacts* and retaining only structural deliberations.

### Infrastructure construction

Given a fixed solution-space instance:

* Discard all UID sorts and identifier states.
* Choose resources as either: `Resource = N` or `Resource = N ⊎ E`.
* For each edge, use its mereology to generate adjacency.

If edges are undirected, adjacency can be generated symmetrically, or orientation can be fixed arbitrarily. Safety properties in the problem space do not depend on which orientation is chosen.

### Forgetting cardinalities and UIDs

Cardinality axioms and UID uniqueness enforce data-model integrity but are irrelevant for defining adjacency and continuity. The problem model only requires that each edge consistently connects two endpoints.

### Paths to trains

A well-formed solution-space path projects to a sequence of concrete nodes and edges via retrieval.

From this sequence, one can construct a train trajectory:

* Consecutive elements yield adjacency witnesses.
* Finite paths are extended to infinite time by stuttering at the final location.

Correctness follows from path well-formedness: alternation and mereology ensure each step corresponds to a valid adjacency.

## Summary

The two models address different concerns:

* The solution modelcaptures how railway networks are represented and reasoned about in software systems.
* The problem model captures how trains physically move through infrastructure over time.

The problem model can be seen as a semantic projection of the solution model, obtained by forgetting identifiers and aggregates and retaining only the connectivity needed for motion. Conversely, the solution model can be understood as a refinement that adds identification, integrity, and specification structure on top of the physical core.
