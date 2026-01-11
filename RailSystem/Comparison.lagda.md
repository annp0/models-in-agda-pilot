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

The solution model can be projected into the problem model by forgetting implementation artefacts and retaining only structural deliberations. Conceptually, this is a semantic projection from a representational ontology (identifiers, aggregates, and data-centric mereology) to an operational ontology (resources, adjacency, and time-indexed occupancy). The projection is conservative with respect to safety: it discards intensional identity disciplines and global registries while preserving precisely the connectivity needed to constrain motion and evaluate invariants over states.

This "forgetful" mapping can be understood as a refinement reversal: the solution space elaborates the same physical core with identification, membership, and retrieval apparatus; the problem space recovers the core by collapsing representational layers into denotations of occupiable structure. Where the solution space emphasizes how we "know" and "name" the network, the problem space emphasizes how agents "are" and "move" within it.

### Infrastructure construction

Given a fixed solution-space instance (a graph, its edge/node aggregates, UID systems, and mereology):

- Ontological choice of resources:
  - `Resource = N` yields an occupancy ontology in which only nodes are occupiable endurants;
  - `Resource = N ⊎ E` yields a richer occupancy ontology in which both nodes and edges can be directly occupied, reflecting the operational reality that trains may be “on track” as well as "at station".
  - This choice is not only technical; it reflects a modelling stance on what counts as a "location" for agents. The projection should be explicit about this stance, since safety invariants (e.g., exclusivity) will quantify over whatever the resource domain declares ontologically occupiable.

- Generating transitions from mereology:
  - The solution space provides undirected incidence via `mereoE : E → Pred NI` and `mereoN : N → Pred EI`. From each edge's endpoints (exactly two node identifiers), construct directed transitions:
    - If `e` connects `{n₁, n₂}`, generate `Transition` elements witnessing movement `n₁ → n₂` and `n₂ → n₁`.
    - If `Resource = N ⊎ E`, additionally allow transitions that enter and exit edges as occupiable resources (e.g., `n₁ → e`, `e → n₂`), yielding fine-grained adjacency that mirrors alternating path semantics.
  - Orientation is a representational convention layered atop undirected incidence. It can be fixed arbitrarily or chosen systematically (e.g., lexicographic on identifiers) without affecting safety reasoning.

- Locality and completeness:
  - The generated `Transition` set must witness all and only the primitive adjacencies required by mereology. This ensures that continuity proofs in the problem space are grounded in the same topological constraints that make paths well-formed in the solution space.

The infrastructure projection performs an ontological selection (what can be occupied) and a structural derivation (how occupiable elements connect) from declarative incidence to operational adjacency.

### Forgetting cardinalities and UIDs

Cardinality axioms, uniqueness of identifiers, and global membership predicates is very important in the solution space: they ensure we can re-identify and retrieve the same entity across observations and registries. The problem space however does not rely much on it; it mainly uses the extensional equality property of atomic resources.

- What is forgotten:
  - UID sorts (`GI`, `EI`, `NI`, …) and their global states (`σuis`).
  - Registry aggregates (`EA`, `NA`) except insofar as they contribute to mereology-derived connectivity.
  - Cardinality ties (`cardP σ ≡ cardPI σuis`) and retrieval correctness witnesses.

- What is preserved:
  - The extensional "shape" of occupancy: which entities are occupiable and how they are adjacent.
  - The structural constraints that are safety-relevant: locality of motion and exclusivity of occupancy.

For movement and occupancy reasoning, continuity and exclusivity depend on adjacency, not on how entities are named. The projection is therefore conservative: it preserves all topological constraints and discards representational commitments not needed for state-level safety invariants.

### Paths to trains

A well-formed solution-space path is an alternating sequence of edge/node identifiers subject to membership and mereological constraints. Through retrieval, such a path is reified as a concrete sequence of edges and nodes; the projection reads this sequence as a "perdurant": a time indexed narrative of being somewhere and then somewhere else.

- The alternation condition (`NI` then `EI` or `EI` then `NI`) is precisely the local adjacency condition: successive elements are incident under mereology. It guarantees that no “jumps” occur in the representational path.

- Correctness by construction:
  - Path well-formedness (alternation, membership, mereology) ensures each successive occupancy pair is supported by a local transition. Thus the continuity proof in the problem space is a semantic shadow of the path’s combinatorial well-formedness.

Basically, we can drop a lot of representation while still preserving the essential semantics to model "motion".


### Category view

One may view the solution space as a category of labeled graphs with mereology and UIDs, and the problem space as a category of transition systems over resources. The projection acts like a functor that:

- Sends nodes/edges to objects (resources).
- Sends incidence to generating morphisms (transitions).
- Sends alternating paths to morphism-composable traces.
- Discards labels (UIDs) but preserves the underlying connectivity used to define morphisms.


### Safety invariants under projection

Exclusivity formulated as "for all distinct agents at time `t`, their resources are different" is invariant under the projection:

- It quantifies over the resource domain selected by the ontology (`N` or `N ⊎ E`).
- It depends only on extensional equality of occupancy, not on identifiers or registries.
- Movement semantics remain local and deterministic with respect to generated transitions, ensuring that exclusivity can be checked and enforced at each instant.

Other structural invariants follow similarly.

### Granularity and refinement

- Coarser segmentation (`Resource = N`) makes stations atomic and tracks mediating but non-occupiable. Safety properties may become conservative, flagging potential conflicts earlier.

- Finer segmentation (`Resource = N ⊎ E` or subdivided edges) externalizes more intermediate configurations, strengthening locality and clarifying where exclusivity applies.

Crucially, the projection respects refinement: finer resource partitions yield more transitions but preserve the same locality principle. Safety is monotone under refinement: more detail cannot hide conflicts; it can only make them explicit.

### Summary

The two models address different concerns:

- The solution model captures how railway networks are represented and reasoned about in software systems: identifiers, aggregates, membership, mereology, etc.

- The problem model captures how trains physically move through infrastructure over time: resources, transitions, etc.

The problem model can be seen as a semantic projection of the solution model, obtained by forgetting identifiers and aggregates and retaining only the connectivity needed for motion. Conversely, the solution model can be understood as a refinement that adds identification and specification structure on top of the physical core.
