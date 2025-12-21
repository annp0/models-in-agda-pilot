Railway systems are critical infrastructure with stringent safety requirements. To reason rigorously about their behaviour, engineers and researchers have, for decades, advocated formal modelling techniques that make domain assumptions explicit and enable logical reasoning about important properties such as collision-freedom and progression. Formal methods in the railway domain have been systematically surveyed and applied to many aspects of signalling, interlocking, scheduling, and control logic. ([1])

These models vary in scope and abstraction, but at the core they all represent:

* A topology of physical resources (tracks, blocks, stations).
* A dynamics governing movement along that topology.
* Interactions between the participants (for example, safety requirements related to occupancy and separation.)

Here we try to define a minimal for moving agents (trains) on a railway infrastructure that is consistent with our intuition and existing literature.


### Modelling the topology of physical resources

At the most fundamental level, a railway network can be viewed as a directed graph:

* Nodes represent locations such as stations, switches, or blocks.
* Edges represent segments of track connecting these locations.

Formalizations in the literature typically start with an abstract representation of topology before introducing dynamics; for instance, standard topology models like the `RailTopoModel` define a systematic representation of railway network elements and their connectivity to support simulation and verification across tools. ([2]) This should be our starting point. Following this, the proposed specs are the following:

* `Station`: a set of discrete waypoints in the network.
* `Track`: a set of directed segments connecting stations.
* `src : Track → Station`: source endpoint of a segment.
* `dst : Track → Station`: destination endpoint of a segment.

This corresponds directly to a connectivity graph. The use of explicit endpoint functions ensures that a track segment always has well-defined endpoints and enables reasoning about adjacency and legal movement (see next section).

### Modeling of Movement Semantics

#### Time and States should be discrete! 

In safety-critical systems, it is common to model behaviour in discrete time for tractability. Even in standards such as ETCS, movement authorities and protected blocks can be reasoned about in discrete steps during verification. The semantics of motion can be given as a state transition system where states are configurations of the system at a discrete instant and transitions capture permitted changes. This is analogous to Kripke structures used in model checking. ([3])

#### Adjacency and Locality of States

When we want a model of "states" with "time" that is close to reality, usually we require some sort of continuity. That is, each of those "states" should only transit into "adjacent states" for each adjacent ticks. It is up to us to define what it means by "adjacent". 

In our case, we want to define "motion" over the existing topology, i.e. we want to define what it means to move "one step" in the network - or in another sense, what "states" are close to each other. In real railway systems:

* A train may stay on its current segment or at a location between control ticks.
* A train moves from a station onto an outgoing track (departure).
* A train moves from the end of a track to the next station (arrival).
* A train may traverse connected segments without stopping if signals and blocks permit.

This aligns with widely used formalisms in discrete event systems (for example DEVS) where adjacency defines permitted local transitions between states, although the formal scheduling time is not continuous. ([4])

So, at any discrete time step:

1. A train may remain at its current location.
2. A train may move from a station to a track whose source matches the station.
3. A train may move from a track to the station at the track’s destination.
4. A train may move from one track to another if the first track’s destination is the second track’s source.

Each rule corresponds to the physically plausible motion of a train over a micro-step of the network topology.

### Agents as Time-Indexed Trajectories

In railway modelling, the behaviour of each train can be formalized as a time-indexed trajectory over the network. This practice is common in formal verification approaches where each train's movement is modelled as a function of time with constraints imposed by signalling and block occupancy rules. ([1])

* A train has a position at each discrete time step.
* This position is either a station or a track segment.
* The train's evolution over time is "continuous".

This perspective is consistent with modelling paradigms used in the analysis of automated train operation systems, where trains are represented as state machines that evolve under local transition relations that respect the network topology.

### Block Occupancy Safety

One of the most fundamental safety principles in rail operations is that two trains should not occupy the same block or track segment at the same time, unless the signalling system explicitly allows it (e.g., moving block systems in ETCS Level 3). Traditional fixed block systems enforce this via signalling systems such as Automatic Block Signalling, which subdivide tracks into sections that behave like safety barriers. ([5])

* If at any time two trains are on tracks, they must be on distinct track segments.
* If either train is at a station, occupancy is permitted (subject to other higher-level constraints).

By encoding these safety constraints directly in the model, one can formally verify that no reachable configuration violates the intended separation property. Many formal tools applied to railway signalling and interlocking use related invariants to prove safety properties over system executions. ([6])

### Compositional Multi-Agent Systems

Modeling multiple trains together introduces the need for compositional reasoning about consistency among agents. Modelling such systems therefore requires compositional reasoning: global safety properties must be derived from the interaction of individual behaviours. This is mirrored in formal railway models that compose multiple agent behaviours (e.g., trains, signals, interlocking logic), often verified using model checking or theorem proving. ([7])

* A network is a finite collection of trains.
* A global consistency predicate asserts that for any pair of distinct trains at any time, the pair satisfies the safety constraint defined above.

This compositional structure is necessary to express and verify properties such as collision avoidance and safe sequencing.

### How close are we to real life?

The specification presented here deliberately abstracts away from several real-world complexities. For example:

- Train length is not modelled explicitly; the position of a train denotes its head rather than its full physical extent.

- Track segmentation can be refined by introducing additional stations or track segments without changing the underlying modelling principles.

- Time granularity and speed are abstracted into discrete steps; finer-grained timing or continuous dynamics could be introduced by refining the time model or the adjacency relation.

These simplifications are intentional. They allow us to isolate the essential structural and behavioural assumptions while preserving extensibility: richer models can be obtained through systematic refinement rather than redesign. However, it is equally important to acknowledge that these abstractions introduce limitations, and that certain real-world edge cases are not faithfully represented at this level:

- a long train simultaneously occupies multiple track segments, and the rear of a train has not yet cleared a block while the head has entered the next one,

- partial overlap between trains occurs during coupling or decoupling operations.

Similarly, the abstraction of track segmentation assumes that track segments are atomic units of occupancy. In real systems, segmentation is often driven by signalling design rather than physical topology, and block boundaries may not align neatly with stations or junctions.

The discrete-time abstraction also limits the model’s ability to represent:

- continuous speed profiles,
- braking distances and stopping curves,
- transient states where safety depends on precise timing rather than topological separation.

Such phenomena are central in detailed operational analyses and performance optimisation, but they lie outside the scope of the present specification.

Despite these limitations, the chosen abstractions are well justified for the intended purpose of this model.

First, the specification is aimed at capturing structural safety properties, such as collision avoidance and mutual exclusion, rather than precise physical dynamics. For these properties, discrete abstractions are both common and effective, as evidenced by their widespread use in formal railway verification literature.

Second, the abstractions are conservative with respect to safety. By treating track segments as indivisible and trains as point-like entities, the model errs on the side of over-approximating potential conflicts rather than missing them. Refinements that introduce train length or finer segmentation can only strengthen the safety guarantees.

Third, and most importantly, the abstractions are refinement-friendly. Each simplification corresponds to a modelling choice that can be systematically relaxed:

- Train length can be introduced by modelling occupancy as a set of segments rather than a single position.

- Track segmentation can be refined without altering the underlying movement semantics.

- Discrete time can be refined into finer steps or replaced by a hybrid discrete–continuous model.

As a result, the present specification should be understood not as a final model of railway operation, but as a foundational layer upon which more detailed models can be built.

### The Universality of our Model: From Railways to Highways

The formal specification introduced so far was motivated by railway systems and their characteristic safety requirements. However, an important observation is that the core movement model itself is agnostic to the transportation domain. The distinction between railways and other transportation systems arises not from the underlying topology or movement semantics, but from the interaction constraints imposed on agents.

In this section, we show that by relaxing the pairwise safety constraint, the same formal model naturally admits an interpretation as a highway/road traffic system, with trains reinterpreted as cars.

#### Shared structural assumptions

At an abstract level, both railway systems and highway systems share several fundamental characteristics:

* A fixed network structure of locations and connecting segments.
* Agents that move along this network over time.
* Physical constraints that prevent arbitrary jumps between unrelated locations.

These shared assumptions are already captured by the core components of the model:

* Infrastructure is represented as a directed graph (`Station`, `Track`, `src`, `dst`).
* Agent motion is constrained by a local adjacency relation.
* Individual agents are described as time-indexed trajectories that respect this adjacency.

Notably, none of these components intrinsically encode rail-specific assumptions such as exclusive occupancy, signalling blocks, or interlocking logic.

#### The role of exclusivity in railway systems

What distinguishes railway systems from road traffic systems is not movement along a network per se, but the exclusive use of infrastructure resources.

In traditional railway operation:

* Track segments (or blocks) are treated as exclusive resources.
* At most one train may occupy a given segment at any time.
* Safety is ensured by enforcing this exclusivity through signalling and interlocking mechanisms.

In the formal model, this intuition is captured entirely by the pairwise consistency constraint, which forbids two trains from occupying the same track segment simultaneously.

Crucially, this constraint is not embedded in the definition of movement or topology. It is imposed separately, at the level of interaction between agents.

#### Removing exclusivity

If the pairwise consistency constraint is removed, the remaining model still describes:

* Agents moving over a directed graph.
* Local, physically plausible motion between adjacent locations.
* Time-indexed trajectories respecting continuity constraints.

However, without exclusivity, multiple agents may occupy the same track segment at the same time. This behaviour is inconsistent with classical railway operation, but it is entirely natural in the context of road traffic systems.

Under this reinterpretation:

* `Station` can be understood as intersections or junctions.
* `Track` can be understood as road segments.
* Trains correspond to cars or other road vehicles.
* Shared occupancy of road segments is permitted.

The same adjacency relation now describes ordinary vehicle motion: entering a road from an intersection, leaving a road into an intersection, or continuing along connected road segments.

Thus, the base model - without additional safety constraints - aligns closely with common abstractions used in traffic flow modelling and road network simulations.


### Separation of movement and policy

This observation highlights a key modelling principle: movement semantics and safety policies should be separated.

* The movement model captures what is physically possible.
* Safety constraints capture what is operationally permitted.

In railway systems, the policy enforces strict exclusivity.
In highway systems, the policy is weaker, allowing shared occupancy while relying on other mechanisms (e.g., speed limits, braking distances, driver behaviour) to avoid collisions.

By isolating exclusivity into a separate consistency predicate, the model allows these different interpretations to coexist without modifying the underlying dynamics.

#### Implications for extensibility

This separation has important consequences:

1. Reuse:
   The same core model can support multiple transportation domains by varying only the interaction constraints.

2. Refinement:
   More sophisticated policies, such as lane-based separation and headway constraints can be added incrementally without redefining movement.

3. Clarity:
   Domain-specific assumptions become explicit rather than implicit, making the model easier to reason about and compare.

In particular, the railway interpretation can be seen as a specialisation of a more general multi-agent movement model on graphs, obtained by strengthening the interaction constraints.

### Citations

[1]: https://link.springer.com/article/10.1007/s10270-025-01276-3 "Models for formal methods and tools: the case of railway ..."
[2]: https://en.wikipedia.org/wiki/RailTopoModel "RailTopoModel"
[3]: https://en.wikipedia.org/wiki/Kripke_structure_%28model_checking%29 "Kripke structure (model checking)"
[4]: https://en.wikipedia.org/wiki/DEVS "DEVS"
[5]: https://en.wikipedia.org/wiki/Automatic_block_signaling "Automatic block signaling"
[6]: https://dl.acm.org/doi/full/10.1145/3520480 "Formal Methods in Railways: A Systematic Mapping Study"
[7]: https://iris.cnr.it/bitstream/20.500.14243/538919/5/terBeek_SoSyM_2025.pdf "Models for formal methods and tools: the case of railway ..."
