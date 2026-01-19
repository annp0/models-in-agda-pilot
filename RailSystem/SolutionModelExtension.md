## Extensions of the Solution-Space Transport Model

The present solution-space model deliberately treats "transport nets" at a high level of abstraction: as graphs with uniquely identified nodes and edges, endowed with mereology, attributes, and well-formed paths.

Therefore, we can outline extensions of that model, which can also be framed as semantic refinements in the sense of domain analysis: each refinement preserves the original conceptual core while increasing descriptive power.

And the extensions remain within the solution space: they concern representation, classification, attributes, and integrity constraints, which are software concepts, and we do not cross into the domain of physical dynamics or behavioural execution.

### 1. Refinement by Transport Kind

The current solution-space model (`RailSystemPaper`) is intentionally kind-agnostic. It introduces graphs, nodes, edges, identifiers, and mereology, but it does not yet distinguish between different transport modalities.

A first refinement direction is to introduce transport kind as an explicit classificatory dimension layered on top of the existing graph ontology.

This refinement does not modify the definition of graphs, nodes, or edges. Rather, it semantically refines over the existing structure: we may introduce a finite set of transport kinds:

* `road`, `rail`, `sea`, `air`

and associate a kind with edges (and optionally nodes) via attributes.

This yields a refinement in which the original graph is understood as a multi-modal carrier structure, rather than as a monolithic network.

### 2. Typed Subgraphs

Rather than treating transport kind as an annotation, a stronger refinement is to stratify the graph into typed subgraphs.

Concretely, we may distinguish a family of graphs:

$$
(G_{\text{road}}, G_{\text{rail}}, G_{\text{sea}}, G_{\text{air}})
$$

such that:

* each $G_k$ is a graph in the sense of `GraphSig`,
* nodes may belong to multiple $G_k$,
* edges belong to exactly one $G_k$.

This preserves the original graph abstraction while sharpening the semantics of multi-modal transport. And it is purely structural: it reorganizes membership, not behaviour.

### 3. Attribute Enrichment of Edges and Nodes

The solution model explicitly anticipates extension: nodes and edges are endurants whose descriptive content is intentionally minimal. This opens a second refinement axis: attribute enrichment.

A refinement may therefore introduce attributes such as:

* geometric attributes: altitude bands (air), depth ranges (sea), corridor widths, ...

* regulatory attributes: controlled airspace, territorial waters international or shared zones.

Crucially, these remain attributes of existing nodes and edges.
They do not alter the underlying graph structure, identifiers, or mereology.

### 4. Refinement of Mereology

The current mereology is deliberately minimal:

* each edge is incident to exactly two nodes,
* each node is incident to one or more edges.

This serves as a foundation for refinement: certain transport domains, particularly air and sea, exhibit junctions that are not naturally binary, like holding patterns, airspace sectors,
and maritime traffic schemes.

A solution-space refinement may therefore introduce compound endurants comprised of compound nodes and aggregate edges, each with their own identifiers and mereological relations to lower level elements.

This mirrors the paper's progression from atomic to compound endurants and remains fully within solution-space ontology.

### 5. Path Semantics as Intentional Artefacts

In the current model, paths are purely combinatorial objects subject to well-formedness constraints. A further refinement is to recognize that paths in solution space are not merely mathematical sequences but intentional artefacts. We may refine the model by classifying paths according to their role:

* planned vs. admissible vs. preferred routes
* regulated routes (airways, shipping lanes)
* emergency / contingency routes

These classifications do not change what a path is, they change how paths are interpreted within the domain.

### 6. Constraints as Domain Knowledge

Many constraints in the current model appear as axioms like cardinality conditions, membership well-formedness, and uniqueness assumptions.

A further refinement is to reify such constraints as explicit domain entities, for example:

* separation constraints (air)
* right-of-way conventions (sea)
* congestion or capacity annotations

