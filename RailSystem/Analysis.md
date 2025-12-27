### Motivation

Railway systems are safety critical infrastructures in which correctness requirements are dominated not by performance or realism, but by structural safety properties. For this reason, railway engineering has long served as a canonical application domain for formal methods. [1](https://dl.acm.org/doi/abs/10.1145/3520480)

The goal of this document is to present a foundational formal model for agents moving on networked infrastructure. While railways serve as the motivating example, the model itself is intentionally abstract. Past lessons [2](https://link.springer.com/article/10.1007/s10270-025-01276-3) taught us that it should capture the minimal structure required to reason about movement, locality, and interaction between multiple agents, without committing prematurely to domain‑specific operational details.

We proceed by gradually introducing structural elements and behavioural constraints, with each addition motivated by the need to express particular classes of properties. More detailed or realistic models should be viewed as extensions of this core, rather than replacements.

### (1) Infrastructure Topology

At the most abstract level, the infrastructure on which agents move is finite and fixed. It constrains where agents may be and how they may move, but does not itself encode behaviour. [3](https://www.railtopomodel.org/files/download/RailTopoModel/180416_uic_irs30100.pdf) [4](https://www.railtopomodel.org)

A naive approach would represent stations as nodes and tracks as edges. While intuitive, this distinction becomes less useful once occupancy and interaction constraints are considered. In particular, both stations and track segments may act as resources whose usage must be reasoned about over time. Treating them differently at the structural level introduces unnecessary asymmetry. [5](https://ceur-ws.org/Vol-2721/paper588.pdf)

We therefore adopt a uniform representation in which all occupiable elements of the infrastructure are modelled in the same way.

The infrastructure is modelled as a directed bipartite graph consisting of:

- a finite set `R` of resources, representing occupiable elements of the infrastructure (including track segments and stations), and

- a finite set `N` of transitions, representing admissible changes between resources.

Each transition connects exactly two resources:

- in : `N -> R`, the source resource, and

- out : `N -> R`, the destination resource.

Intuitively, a resource corresponds to a portion of the infrastructure that may be occupied for a non‑zero duration, while a transition represents a momentary change of occupancy.

This representation is compatible with event‑based and discrete‑event models commonly used in transportation and routing systems, and avoids ambiguity about where exclusivity constraints should apply.

### (2) Time and States

Our interests, for this model, are mostly structural. In particular, we are concerned with invariants such as exclusivity of resources, admissible adjacency of movement, and the absence of unsafe configurations. These properties are defined over configurations of the system and their evolution, rather than over continuous trajectories or physical dynamics.

For such properties, it is sufficient to reason about system behaviour as a sequence of abstract instants, each representing a configuration in which occupancy and movement constraints can be evaluated. This perspective is standard in the verification of safety-critical systems, where behaviour is analysed as a transition between well-defined states rather than as continuous motion.

We therefore model system evolution in discrete time. Let `T = {0, 1, 2, ...}` denote the set of time steps. Each element of `T` corresponds to an abstract control or observation instant at which the global configuration of the system is considered.

This choice aligns naturally with state-transition formalisms commonly used in model checking [6](https://mitpress.mit.edu/9780262038836/model-checking) [7](https://kilthub.cmu.edu/articles/journal_contribution/European_Train_Control_System_A_Case_Study_in_Formal_Verification/6605291/files/12095732.pdf), where systems are represented as sequences of configurations linked by admissible transitions, and safety properties are expressed as invariants over these configurations.

### (3) Agent Positions as Time-Indexed States

Given this discrete notion of time, the state of an individual agent at a time step must record which part of the infrastructure it occupies. Since all occupiable elements of the infrastructure are uniformly represented as resources, an agent's state can be captured directly as a resource identifier.

Let Agent denote the finite set of agents (e.g. trains). We define the position of an agent as a function

```
pos : Agent x T -> R
```

where `pos(a, t)` denotes the resource occupied by agent `a` at time `t`s.

This representation makes explicit the assumptions required for safety reasoning:

- at each time step, the occupancy of resources is well-defined;

- interaction constraints, such as mutual exclusion, can be expressed as predicates over positions at the same time step;

- movement can be described as a relation between successive positions in time.

In this way, an agent’s behaviour is naturally interpreted as a time-indexed trajectory through the resource graph, while global safety properties are expressed as invariants over collections of such trajectories.

### (4) Movement Semantics

The purpose of the movement semantics is not to describe physical dynamics, but to characterise which changes of configuration are admissible between successive time steps. In particular, the movement relation must be rich enough to express progress through the infrastructure, while remaining constrained enough to support locality based safety reasoning. [8](https://digital-library.theiet.org/doi/pdf/10.1049/cp.2016.0511?download=true&utm_source=chatgpt.com)

Two requirements guide its formulation.

First, movement must respect the topology of the infrastructure. Agents are constrained to move along the physical network and cannot appear arbitrarily at unrelated locations. Any admissible evolution of positions must therefore be compatible with the connectivity structure of the resource graph.

Second, movement must be locally incremental. Since time is discretised into abstract instants at which occupancy is evaluated, each step should correspond to a minimal change of position. Allowing an agent to traverse multiple infrastructure elements in a single step would collapse distinct intermediate configurations and prevent precise reasoning about interaction and exclusion.

These requirements together suggest that movement should be defined as a relation between successive positions that is mediated explicitly by the transition structure of the infrastructure.

Let `a ∈ Agent` and `t ∈ T`. Between time steps `t` and `t+1`, the position of `a` may evolve in one of the following ways:

- the agent remains on the same resource, `pos(a, t+1) = pos(a, t)`.

- the agent traverses a transition n ∈ N such that `in(n) = pos(a, t)`, and `out(n) = pos(a, t+1)`.

No other changes of position are permitted.

This definition ensures that every movement step corresponds either to maintaining occupancy of the current resource or to traversing an explicitly represented transition. As a result, all motion is grounded in the infrastructure topology.

By restricting admissible movement to stasis and single transitions, the model enforces locality of motion: agents may only move to resources that are directly connected in the graph. Arbitrary jumps across the infrastructure are excluded by construction.

Although time is discrete, this constraint provides a notion of continuity at the level of the model. An agent’s trajectory is a sequence of adjacent resources, and intermediate configurations are never skipped. This property is essential for reasoning about interaction between agents, since safety constraints such as mutual exclusion are evaluated at every step where resource occupancy may change.

In this way, the movement semantics complements the discrete state structure introduced earlier, yielding a state-transition system in which both motion and interaction can be analysed using standard techniques.

### (5) Single Agent Behaviour

Before considering interaction between agents, it is useful to characterise the behaviour of a single agent in isolation. This serves two purposes. First, it makes explicit which aspects of behaviour are determined solely by the infrastructure and movement semantics. Second, it allows interaction constraints to be introduced later without entangling them with basic motion.

Given the definitions introduced so far, the behaviour of a single agent is completely determined by the movement semantics. At each time step, the agent occupies a resource, and between successive steps its position evolves according to the adjacency constraints induced by the transition structure.

Formally, the evolution of an agent corresponds to a time-indexed sequence of resources such that each successive pair is either identical or connected by a transition. In other words, a single agent traces a path through the resource graph over discrete time.

At this level, no additional constraints are imposed. The model characterises which evolutions are structurally admissible given the infrastructure, without yet expressing any safety or coordination requirements. This distinction is deliberate: it separates the description of individual motion from assumptions about how multiple agents may interact.

### (6) Multi Agent Systems

When multiple agents are present, the system must represent their joint configuration at a given time. Since the state of each agent is given by its occupied resource, a global system state at time `t` can be described as the collection of all agent positions:

```
state(t) = { pos(a, t) | a ∈ Agent }
```

The evolution of the system consists of the simultaneous evolution of all agent positions from one time step to the next, subject to the movement semantics defined earlier.

At this stage, the global state space is simply the Cartesian product of individual agent states. No assumptions are made yet about how agents affect one another.

#### Interaction via Occupancy Constraints

In many infrastructure based systems, resources are not merely locations but represent elements whose use must be coordinated. In railway systems in particular, track segments and stations are treated as exclusive: they may be occupied by at most one train at any given time. [9](https://dl.ifip.org/db/conf/coordination/coordination2010/Vanit-Anunchai10.pdf) [10](https://www.sciencedirect.com/science/article/pii/S0167642316300570)

Given that all occupiable infrastructure elements are modelled uniformly as resources, such coordination requirements can be expressed directly as constraints on global states. Specifically, the exclusivity requirement can be formulated as a state invariant:

- For all distinct agents `a ≠ b` and all times `t`, `pos(a, t) ≠ pos(b, t)`.

This invariant rules out global configurations in which two agents occupy the same resource simultaneously. Importantly, it does so without altering the movement semantics themselves. Individual agents still evolve according to the same local rules; only certain joint configurations are deemed inadmissible.

#### Compositional Interpretation

The resulting structure admits a compositional interpretation. Each agent evolves independently according to the movement semantics induced by the infrastructure, while interaction between agents is captured entirely by invariants over global states.

From this perspective, safety properties such as collision avoidance are not encoded as part of the motion model, but arise from restrictions on which combinations of individual behaviours are allowed. This mirrors common practice in formal railway modelling, where signalling and interlocking logic constrain otherwise independent train movements by ruling out unsafe configurations.

By separating individual behaviour from interaction constraints, the model supports modular reasoning: properties of single-agent motion can be established independently, and global safety properties can be analysed by studying how these behaviours compose under the imposed invariants.

### Scope and Relation to Real life

The model presented here operates at a deliberately abstract level. Its purpose is not to reproduce the full physical behaviour of railway systems, but to isolate a small set of structural assumptions that are sufficient to reason about movement and safety at the level of infrastructure occupancy.

As a consequence, several aspects of real-world operation are not represented explicitly.

First, trains are modelled as occupying a single resource at each time step. This can be interpreted as modelling the position of a train's head rather than its full physical extent. Effects arising from train length, such as simultaneous occupancy of multiple track segments or delayed clearance of a block by the rear of the train, are therefore not captured directly.

Second, infrastructure segmentation is treated abstractly. Resources are assumed to be atomic units of occupancy, and their granularity is not fixed by physical topology. In real railway systems, segmentation is often driven by signalling design and operational considerations, and block boundaries need not align neatly with stations, junctions, or physical track segments. At the present level of abstraction, such distinctions are intentionally suppressed.

Third, time is treated discretely, and movement is expressed as transitions between configurations. This precludes direct representation of continuous phenomena such as speed profiles, braking curves, or safety constraints that depend on precise timing rather than topological separation.

These omissions are not accidental. They reflect the intended focus of the model.

The primary aim is to capture structural safety properties, in particular, properties related to occupancy and admissible movement through the infrastructure. For such properties, discrete abstractions are widely used and have proven effective in formal railway verification. Continuous dynamics are orthogonal to this level of reasoning.

Moreover, the abstractions adopted here are conservative with respect to safety. By treating resources as indivisible and agents as occupying a single resource at a time, the model tends to over approximate potential conflicts rather than conceal them. Introducing additional detail, such as train length or finer segmentation, can only strengthen safety guarantees by making conflicts more explicit.

Finally, the model is designed to admit systematic extension. Each abstraction corresponds to a modelling choice that can be relaxed without altering the underlying movement semantics:

- train length can be incorporated by allowing agents to occupy sets of resources rather than a single one,

- infrastructure detail can be increased by subdividing resources,

- discrete time can be refined or combined with continuous dynamics in a hybrid model.

For these reasons, the specification should be understood not as a complete model of railway operation, but as a foundational layer. It provides a stable structural core upon which more detailed and domain-specific models can be constructed through refinement rather than redesign.

### Generality of the Movement Model

Although the model has been developed with railway systems in mind, its core structure does not rely on assumptions that are specific to rail transport. In particular, the definitions of infrastructure, movement, and agent evolution are independent of any particular safety or signalling regime.

This becomes apparent when examining which assumptions are encoded directly in the model and which are introduced separately.

At the structural level, the model consists of:

- a fixed network of resources connected by transitions,

- agents whose positions evolve over time subject to adjacency constraints,

- a discrete state-transition structure that records successive configurations.

These components capture basic properties of agents moving on constrained infrastructure: locality of motion, continuity with respect to the network topology, and well-defined configurations at each time step. None of them impose restrictions on how many agents may occupy a given resource simultaneously, nor do they encode railway-specific concepts such as signalling blocks or interlocking logic.

The distinction between railway systems and other transportation systems therefore does not arise from the movement semantics themselves, but from additional constraints placed on joint configurations.

#### Exclusivity as an Interaction Constraint

In classical railway operation, infrastructure resources are treated as exclusive. Track segments and stations are protected so that at most one train may occupy a given resource at any time, and safety is enforced by ensuring that this exclusivity is never violated.

Within the present framework, this requirement appears naturally as a constraint on global states: configurations in which two agents occupy the same resource are ruled out. Importantly, this constraint is imposed independently of the movement semantics. Individual agents continue to evolve according to the same local rules; only certain combinations of their positions are disallowed.

This separation makes clear that exclusivity is not a property of motion itself, but of how multiple agents are permitted to coexist on the infrastructure.

#### Alternative Interpretations

If the exclusivity constraint is removed, the remaining structure still describes agents moving locally on a network over time. Positions evolve along transitions, configurations are well-defined at each step, and trajectories remain continuous with respect to the topology.

Such behaviour is incompatible with traditional railway safety assumptions, but it corresponds naturally to road traffic systems. Under this interpretation:

- resources correspond to road segments or intersections,

- multiple agents may occupy the same resource,

- motion is governed by the same adjacency rules.

Collision avoidance and spacing are no longer enforced structurally, but are deferred to other mechanisms that lie outside the scope of the present model.

From this perspective, railway systems can be understood as a special case obtained by strengthening the interaction constraints imposed on an otherwise general movement model.

#### Movement and Policy

This observation reflects a broader modelling principle: movement semantics and operational policy are best treated separately.

The movement semantics describe which changes of position are physically admissible given the infrastructure. Interaction policies describe which joint configurations are acceptable given safety or operational requirements. By isolating these concerns, the model allows different interpretations to be obtained without modifying the underlying dynamics. This separation has several consequences.

First, the same core structure can be reused across transportation domains by varying only the constraints imposed on global states.

Second, additional policies, such as lane-based separation, headway constraints, or priority rules, can be introduced incrementally as refinements, without redefining the movement model.

Finally, domain-specific assumptions remain explicit. The distinction between railway and non-railway systems is expressed as a difference in interaction constraints rather than being embedded implicitly in the structure of motion.

In this sense, the railway interpretation emerges as a specialisation of a more general multi-agent movement model on graphs, obtained by strengthening the conditions under which agents may jointly occupy the infrastructure.
