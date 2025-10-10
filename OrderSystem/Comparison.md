## Abstract Model

An order processing system consists of the following elements.

### Basic Structure

1. Entities and Types.
   - Customer with a unique identifier.
   - Item with name/description and cost.
   - Payment as an abstract concept with two concrete types Cash and Credit, each with an amount.
   - Order with a status (success/failure), exactly one customer reference, one or more items, and one or more payments.
   - Status is an enumeration with two values: success and failure.

2. Customer identifiers are unique within the system.

3. Each order references exactly one customer, and that customer must exist.

4. Each order contains one or more items.

5. Each order contains one or more payments.

6. Each payment belongs to exactly one order.

7. All payments are of a valid subtype (Cash or Credit).

8. Every order has a status in {success, failure}.

### Operations

9. Core Operations.
   - Determine order status.
   - Identify the customer for a given order.
   - Calculate the total cost of an order.
   - Verify payment validity or classify payments by subtype.

### Guarantees and Verification

10. The model should support checking/ensuring the above constraints (e.g., facts/checks in Alloy; types/proofs in Agda).

### Features and Characteristics

We reuse the same modeling criteria as in the file system:

- Features:
  - Mapping Feature: The model is based on the common notion of e-commerce order systems.
  - Reduction Feature: We keep only essentials (IDs, items, payments, status) and omit deployment-specific details (tax rules, shipping, currencies).
  - Pragmatic Feature: The model is usable for reasoning about structure and basic operations.

- Characteristics:
  - Abstraction: Unnecessary operational and infrastructure details are omitted.
  - Understandability: Simple entities, relations, and multiplicities.
  - Accuracy: Captures uniqueness, multiplicities, subtyping, and ownership.
  - Predictiveness: Allows checking ownership and multiplicities.
  - Inexpensiveness: Much cheaper than implementing a real order backend; suitable for early validation.

## Implementation

Below, each specification item is realized in Alloy and in Agda.

### Spec 1: Entities and Types (Customer, Item, Payment, Cash, Credit, Order, Status)

#### Alloy Implementation

In Alloy, entities are modeled as `sig`s (signatures), which represent sets of objects. Relationships between entities are expressed as fields within these signatures. The `Status` enumeration is defined using `enum`.

```alloy
sig Customer { id: Int } { id > 0 }  // Customers have positive IDs
sig Item { name: String, cost: Int }  // Items have a name and cost

abstract sig Payment { amount: Int }  // Payments have an amount
sig Cash extends Payment {}  // Cash is a subtype of Payment
sig Credit extends Payment {}  // Credit is a subtype of Payment

sig Order {
  status: Status,  // Each order has a status
  customer: Customer,  // Each order references a customer
  items: some Item,  // Each order contains at least one item
  payments: some Payment  // Each order contains at least one payment
}

enum Status { success, failure }  // Status is an enumeration
```

#### Key Features of the Alloy Model:

1. Each `sig` represents a set of objects. For example, `Customer` is a set of all customers in the system.
2. Relationships between entities are modeled as fields. For instance, the `customer` field in `Order` links an order to a specific customer.
3. The `Payment` signature is abstract, and `Cash` and `Credit` extend it, creating a subtype hierarchy.
4. The `Status` enumeration explicitly defines the possible states of an order (`success` or `failure`).


#### Agda Implementation

In Agda, entities are modeled as records or data types. Relationships between entities are expressed as fields within these records. Enumerations are defined using `data`.

```agda
data Status : Set where
  success failure : Status  -- Status is an enumeration

record Customer : Set where
  eta-equality
  field id : ℕ  -- Customers have a unique ID (natural number)

record Item : Set where
  field
    name : String  -- Items have a name
    cost : Float   -- Items have a cost

record Payment : Set where
  field amount : Float  -- Payments have an amount

record Cash : Set where
  field amount : Float  -- Cash payments have an amount

record Credit : Set where
  field amount : Float  -- Credit payments have an amount

record Order : Set where
  field
    status   : Status      -- Each order has a status
    customer : Customer    -- Each order references a customer
    items    : List⁺ Item  -- Each order contains a non-empty list of items
    payments : List⁺ Payment  -- Each order contains a non-empty list of payments
```

#### Key Features of the Agda Model:
1. Each entity is modeled as a record, which groups related fields together. For example, `Customer` is a record with a single field `id`.
2. Relationships between entities are expressed as fields within records. For instance, the `customer` field in `Order` links an order to a specific customer.
3. `Cash` and `Credit` are separate records, and their relationship to `Payment` is established through conversion functions (see Spec 7).
4. The `Status` enumeration is defined as a `data` type with two constructors: `success` and `failure`.
5. The `List⁺` type ensures that `items` and `payments` are non-empty, enforcing constraints at the type level.

#### Comparison

| Feature                  | Alloy                                                                                    | Agda                                                                                     |
|--------------------------|-------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------|
| **Entity Representation** | Entities are sets (`sig`s).                                                              | Entities are records or data types.                                                     |
| **Relationships**         | Relationships are fields within `sig`s.                                                  | Relationships are fields within records.                                                |
| **Subtyping**             | Subtyping is modeled using `abstract sig` and `extends`.                                  | Subtyping is modeled using separate records and conversion functions.                   |
| **Enumerations**          | Enumerations are defined using `enum`.                                                   | Enumerations are defined using `data`.                                                  |
| **Non-Empty Collections** | Multiplicities (`some`) enforce non-emptiness.                                            | The `List⁺` type enforces non-emptiness at the type level.                               |

#### Strengths and Weaknesses

#### Alloy
- **Strengths**:
  - Subtyping is explicit and enforced structurally through the `abstract sig` and `extends` hierarchy.
  - Relationships are naturally expressed as fields, making the model concise and intuitive.
  - Multiplicities (`some`, `one`, etc.) provide a clear way to enforce constraints like non-emptiness.

- **Weaknesses**:
  - Alloy does not enforce constraints like non-emptiness at the type level; these are only checked during analysis.
  - Enumerations (`enum`) are less flexible than Agda's `data` types, which can include additional structure or proofs.

#### Agda
- **Strengths**:
  - Constraints like non-emptiness are enforced at the type level using `List⁺`, ensuring correctness by construction.
  - Enumerations (`data`) are more flexible and can include additional structure or proofs.
  - The use of dependent types allows for richer and more precise modeling.

- **Weaknesses**:
  - Subtyping is not enforced structurally; instead, it relies on disciplined use of conversion functions (e.g., `cash2Pay`).
  - Relationships between entities are less concise compared to Alloy's field-based approach.


### Spec 2: Unique Customer Identifiers

This section compares how the uniqueness of customer identifiers is enforced in Alloy and Agda.

#### Alloy Implementation

In Alloy, the uniqueness of customer identifiers is enforced globally using a `fact`. The `fact` ensures that no two distinct customers have the same `id`.

```alloy
sig Customer { id: Int } { id > 0 }  // Customers have positive IDs

fact uniqueCustomerIds {
  no disj c1, c2: Customer | c1.id = c2.id
}
```

#### Key Features of the Alloy Model:
1. The `fact uniqueCustomerIds` ensures that the `id` field is unique across all instances of `Customer`.
2. The uniqueness is expressed declaratively, and Alloy's SAT solver checks this constraint during analysis.
3. The additional constraint `id > 0` ensures that all customer IDs are positive integers.

#### Agda Implementation

In Agda, the uniqueness of customer identifiers is not enforced globally by default. Instead, the model provides tools to reason about equality of customers, enabling uniqueness to be proven at a higher level (e.g., within a "system" wrapper).

```agda
record Customer : Set where
  eta-equality
  field id : ℕ  -- Customers have a unique ID (natural number)

-- Decidable equality for customers
customer-equal? : Customer → Customer → Bool
customer-equal? x y = Customer.id x Nat.≡ᵇ Customer.id y

customer-equal-dec : (x y : Customer) → Dec (x ≡ y)
customer-equal-dec x y = customer-equal? x y because customer-equal-reflects x y
```

#### Key Features of the Agda Model:
1. The `customer-equal?` function provides a Boolean test for equality of customers based on their `id` field.
2. The `customer-equal-dec` function provides a decidable equality proof, allowing reasoning about customer uniqueness in a formal system.
3. To enforce global uniqueness, one could define a `System` record containing a collection of customers and a proof that their IDs are unique.

Example of a potential `System` record:
```agda
record System : Set where
  field
    customers : List Customer
    uniqueIDs : AllUnique (map Customer.id customers)
```

#### Comparison

| Feature                  | Alloy                                                                                     | Agda                                                                                     |
|--------------------------|-------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------|
| **Global Uniqueness**     | Enforced globally using the `fact uniqueCustomerIds`.                                     | Not enforced globally; requires a `System` wrapper with a proof of uniqueness.           |
| **Equality**              | Implicitly based on the `id` field; no explicit equality function provided.               | Explicit equality function (`customer-equal?`) and decidable equality proof (`customer-equal-dec`). |
| **Constraint Checking**   | Checked declaratively during analysis using Alloy's SAT solver.                          | Requires explicit proofs or reasoning in a higher-level system.                          |

#### Strengths and Weaknesses

#### Alloy
- **Strengths**:
  - Global uniqueness is enforced declaratively and automatically checked during analysis.
  - The constraint is simple and concise, requiring no additional infrastructure.

- **Weaknesses**:
  - Alloy does not provide a way to extract or reason about equality proofs; it only checks constraints during analysis.
  - The model assumes that the SAT solver will find counterexamples if the constraint is violated, but it does not provide constructive guarantees.

#### Agda
- **Strengths**:
  - Decidable equality and proof extraction enable formal reasoning about customer uniqueness.
  - The model is constructive, allowing for explicit proofs of uniqueness within a `System` wrapper.

- **Weaknesses**:
  - Global uniqueness is not enforced by default and requires additional infrastructure (e.g., a `System` record).
  - The approach is more verbose and requires more effort to model and prove.

### Spec 3 : Order–Customer Association

This section compares how the association between orders and customers is enforced in Alloy and Agda.

#### Alloy Implementation

In Alloy, the association between orders and customers is enforced through field typing. Each `Order` has a `customer` field that references a `Customer`. A `check` ensures that all orders reference valid customers.

```alloy
sig Order {
  customer: Customer  // Each order references exactly one customer
}

check CustomersExist {
  all o: Order | o.customer in Customer
}
```

#### Key Features of the Alloy Model:
1. The `customer` field ensures that each order references exactly one customer.
2. The `check CustomersExist` ensures that all referenced customers exist in the system.

#### Agda Implementation

In Agda, the association between orders and customers is enforced by construction. The `customer` field in the `Order` record is of type `Customer`, ensuring that each order references exactly one customer.

```agda
record Order : Set where
  field
    customer : Customer  -- Each order references exactly one customer
```

#### Key Features of the Agda Model:
1. The type system guarantees that only valid `Customer` instances can be assigned to the `customer` field.

#### Comparison

| Feature                  | Alloy                                                                                     | Agda                                                                                     |
|--------------------------|-------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------|
| **Association Enforcement** | Enforced declaratively through field typing and verified with a `check`.                 | Enforced by construction through the type of the `customer` field.                       |



### Spec 4: Non-empty Items

This section compares how the non-emptiness of items in an order is enforced in Alloy and Agda.

#### Alloy Implementation

In Alloy, the non-emptiness of items is enforced using the `some` multiplicity keyword. This ensures that each order contains at least one item.

```alloy
sig Order {
  items: some Item  // Each order contains at least one item
}
```

#### Key Features of the Alloy Model:
1. The `some` multiplicity ensures that the `items` field is non-empty.

#### Agda Implementation

In Agda, the non-emptiness of items is enforced at the type level using the `List⁺` type, which represents non-empty lists.

```agda
record Order : Set where
  field
    items : List⁺ Item  -- Each order contains a non-empty list of items
```

#### Key Features of the Agda Model:
1. The `List⁺` type ensures that the `items` field is non-empty by construction.

#### Comparison

| Feature                  | Alloy                                                                                     | Agda                                                                                     |
|--------------------------|-------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------|
| **Non-emptiness Enforcement** | Enforced declaratively using the `some` multiplicity.                                   | Enforced by construction using the `List⁺` type.                                         |

### Spec 5: Non-empty Payments

This section compares how the non-emptiness of payments in an order is enforced in Alloy and Agda.

#### Alloy Implementation

In Alloy, the non-emptiness of payments is enforced using the `some` multiplicity keyword. This ensures that each order contains at least one payment.

```alloy
sig Order {
  payments: some Payment  // Each order contains at least one payment
}
```

#### Key Features of the Alloy Model:
1. The `some` multiplicity ensures that the `payments` field is non-empty.

#### Agda Implementation

In Agda, the non-emptiness of payments is enforced at the type level using the `List⁺` type.

```agda
record Order : Set where
  field
    payments : List⁺ Payment  -- Each order contains a non-empty list of payments
```

#### Key Features of the Agda Model:
1. The `List⁺` type ensures that the `payments` field is non-empty by construction.

#### Comparison

| Feature                  | Alloy                                                                                     | Agda                                                                                     |
|--------------------------|-------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------|
| **Non-emptiness Enforcement** | Enforced declaratively using the `some` multiplicity.                                   | Enforced by construction using the `List⁺` type.                                         |


### Spec 6: Payment Ownership (each Payment in exactly one Order)

This section compares how the ownership of payments by orders is enforced in Alloy and Agda.

#### Alloy Implementation

In Alloy, the ownership of payments is enforced using a `fact`. The `fact` ensures that each payment belongs to exactly one order.

```alloy
fact paymentsInOneOrder {
  all p: Payment | one o: Order | p in o.payments
}
```

#### Key Features of the Alloy Model:
1. The `fact paymentsInOneOrder` ensures that each payment is associated with exactly one order.

#### Agda Implementation

In Agda, payment ownership is not modeled directly. To enforce ownership, one could index `Payment` by its owning `Order` or record an ownership relation in a `System` type and prove functionality.

```agda
record Payment : Set where
  field
    amount : Float

record System : Set where
  field
    payments : List (Σ Order Payment)  -- Payments indexed by their owning order
```

#### Key Features of the Agda Model:
1. Ownership can be modeled explicitly using indexed types or a `System` wrapper.

#### Comparison

| Feature                  | Alloy                                                                                     | Agda                                                                                     |
|--------------------------|-------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------|
| **Ownership Enforcement** | Enforced declaratively using a `fact`.                                                    | Requires explicit modeling using indexed types or a `System` wrapper.                   |

### Spec 7: Valid Payment Subtyping (Cash or Credit)

This section compares how valid payment subtyping is enforced in Alloy and Agda.

#### Alloy Implementation

In Alloy, subtyping is enforced structurally using an `abstract sig` and its `extends` subtypes. A `check` can be used to verify that all payments are of valid subtypes.

```alloy
abstract sig Payment { amount: Int }
sig Cash extends Payment {}
sig Credit extends Payment {}

check PaymentSubtypes {
  all p: Payment | p in Cash or p in Credit
}
```

#### Key Features of the Alloy Model:
1. Subtyping is enforced structurally through the `abstract sig` and `extends` hierarchy.

#### Agda Implementation

In Agda, subtyping is not enforced structurally. Instead, conversion functions are used to embed `Cash` and `Credit` into `Payment`.

```agda
record Payment : Set where
  field amount : Float

record Cash : Set where
  field amount : Float

record Credit : Set where
  field amount : Float

cash2Pay : Cash → Payment
cash2Pay c = record { amount = Cash.amount c }

cred2Pay : Credit → Payment
cred2Pay c = record { amount = Credit.amount c }
```

#### Key Features of the Agda Model:
1. Subtyping is modeled using conversion functions rather than structural inheritance.

#### Comparison

| Feature                  | Alloy                                                                                     | Agda                                                                                     |
|--------------------------|-------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------|
| **Subtyping Enforcement** | Enforced structurally using `abstract sig` and `extends`.                                 | Modeled using conversion functions.                                                     |


### Spec 8: Status Well-Formedness

This section compares how the well-formedness of order statuses is enforced in Alloy and Agda.

#### Alloy Implementation

In Alloy, the well-formedness of statuses is enforced using an `enum`. A `check` ensures that all orders have valid statuses.

```alloy
enum Status { success, failure }

sig Order {
  status: Status
}

check ValidStatus {
  all o: Order | o.status in Status
}
```

#### Key Features of the Alloy Model:
1. The `enum` ensures that statuses are restricted to valid values.

#### Agda Implementation

In Agda, the well-formedness of statuses is enforced at the type level using a `data` type.

```agda
data Status : Set where
  success failure : Status

record Order : Set where
  field
    status : Status
```

#### Key Features of the Agda Model:
1. The `Status` type ensures that only valid statuses can be assigned to the `status` field.

#### Comparison

| Feature                  | Alloy                                                                                     | Agda                                                                                     |
|--------------------------|-------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------|
| **Well-formedness Enforcement** | Enforced declaratively using an `enum`.                                               | Enforced by construction using a `data` type.

### Spec 9: Core Operations (status, customer, total cost, validity)

This section compares how core operations such as determining order status, identifying the customer for an order, calculating the total cost, and verifying payment validity are implemented in Alloy and Agda.

#### Alloy Implementation

In Alloy, core operations are modeled declaratively. Relationships and constraints are asserted rather than computed. For example, the total cost of an order could be represented as a field or derived through assertions.

```alloy
sig Item {
  cost: Int  // Cost of an item
}

sig Order {
  items: some Item,  // Each order contains at least one item
  total: Int         // Total cost of the order
}

fact totalCost {
  all o: Order | o.total = sum[o.items.cost]
}
```

#### Key Features of the Alloy Model:
1. Operations like `totalCost` are expressed declaratively as facts or constraints.
2. Alloy does not compute values directly but ensures consistency through assertions.
3. Queries such as identifying the customer for an order or verifying payment validity would require additional constraints or checks.

#### Agda Implementation

In Agda, core operations are implemented as executable functions. For example, the total cost of an order can be computed directly, and queries can be performed using functions.

```agda
-- Sum of non-empty list of items
sum⁺ : List⁺ Item → Float
sum⁺ (x ∷ xs) = Item.cost x + sum xs

-- Total cost of an order
getCost : Order → Float
getCost o = sum⁺ (Order.items o)

-- Query orders by customer
queryOrders : List Order → Customer → List Order
queryOrders os c = filter (λ o → Order.customer o ≡ c) os
```

#### Key Features of the Agda Model:
1. Operations like `getCost` are implemented as executable functions.
2. Queries such as filtering orders by customer are straightforward to implement using higher-order functions.
3. Agda's type system ensures correctness of operations, e.g., `List⁺` guarantees non-empty lists for cost calculations.


#### Comparison

| Feature                  | Alloy                                                                                     | Agda                                                                                     |
|--------------------------|-------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------|
| **Total Cost Calculation** | Declaratively modeled as a constraint (`fact totalCost`).                                 | Computed directly using executable functions (`getCost`).                                |
| **Querying**              | Requires additional constraints or checks.                                                | Implemented as functions (e.g., `queryOrders`).                                          |
| **Validation**            | Ensured through declarative assertions.                                                   | Ensured through type-level guarantees and executable logic.                              |

### Spec 10: Verification Modality

This section compares how verification of constraints and guarantees is supported in Alloy and Agda.

#### Alloy Implementation

In Alloy, verification is performed using `check` and `run` commands. These commands allow bounded verification of constraints and exploration of possible instances.

```alloy
check NonEmptyItemsPayments {
  all o: Order | some o.items and some o.payments
}

run {} for 5 but 3 Int
```

#### Key Features of the Alloy Model:
1. Verification is automated and bounded, relying on SAT solvers to find counterexamples or generate instances.
2. The `check` command ensures that constraints hold within the specified bounds.
3. The `run` command generates instances that satisfy the model's constraints.

#### Agda Implementation

In Agda, verification is performed through type-level guarantees and explicit proofs. Constraints are encoded in types, and global properties can be proven within a `System` wrapper.

```agda
record System : Set where
  field
    orders : List Order
    allValid : All (λ o → validOrder o) orders

validOrder : Order → Bool
validOrder o = not (null (Order.items o)) ∧ not (null (Order.payments o))
```

#### Key Features of the Agda Model:
1. Verification is constructive, relying on type-level guarantees and explicit proofs.
2. Constraints like non-emptiness are enforced at the type level, eliminating the need for runtime checks.
3. Global properties (e.g., all orders are valid) can be proven explicitly within a `System` wrapper.

#### Comparison

| Feature                  | Alloy                                                                                     | Agda                                                                                     |
|--------------------------|-------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------|
| **Verification Method**   | Automated, bounded verification using SAT solvers (`check`, `run`).                       | Constructive verification through type-level guarantees and explicit proofs.             |
| **Constraint Checking**   | Declarative constraints are checked automatically.                                        | Constraints are encoded in types or proven explicitly.                                   |
| **Instance Generation**   | Instances are generated using the `run` command.                                          | No instance generation; focuses on correctness by construction.                         |

### Summary

#### The Alloy Model (Full view, for reference)

- Entities and constraints are as shown above.
- The model includes verification checks:
```alloy
check ValidStatus { all o: Order | o.status in Status }
check CustomersExist { all o: Order | o.customer in Customer }
check NonEmptyItemsPayments { all o: Order | some o.items and some o.payments }
check PaymentSubtypes { all p: Payment | p in Cash or p in Credit }
run {} for 5 but 3 Int
```

Summary mapping:
- Specs 1, 3–5, 7–8 by signature/multiplicity.
- Spec 2 and 6 by `fact`s.
- Spec 10 by `check`/`run`.


#### The Agda Model (Full view, for reference)

- Concrete records for entities; List⁺ for non-emptiness.
- Executable operations and customer equality with reflection.

Summary mapping:
- Specs 1, 3–5, 8 by types.
- Spec 7 by disciplined construction via `cash2Pay`/`cred2pay`.
- Spec 9 by `getCost`, `query`.
- Spec 2 and 6 require a System wrapper to enforce and prove globally.
- Spec 10 via types and proofs (no automated counterexample search).

## Comparison per Specification

| Spec # | Requirement                                  | Agda (OrderSystem.lagda.md)                                                                                     | Alloy (OrderSystem.als)                                                                               |
| ------ | -------------------------------------------- | ---------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------- |
| 1      | Entities and types                           | Concrete records and Status datatype; non-empty collections with List⁺.                                          | Signatures; abstract Payment with Cash/Credit; Status enum.                                           |
| 2      | Unique customer IDs                          | Not enforced globally; decidable equality provided to prove uniqueness over a system-level collection.           | Enforced via `fact uniqueCustomerIds`.                                                                |
| 3      | Order–Customer association                   | `customer : Customer` ensures exactly one by construction.                                                       | `customer: Customer` field; simple check for existence.                                               |
| 4      | Non-empty items                              | `items : List⁺ Item` enforces non-emptiness by type.                                                             | `items: some Item` multiplicity.                                                                      |
| 5      | Non-empty payments                           | `payments : List⁺ Payment` enforces non-emptiness by type.                                                       | `payments: some Payment` multiplicity.                                                                |
| 6      | Payment belongs to exactly one order         | Not modeled; would require indexed payments or a system-level ownership relation and proofs.                     | `fact paymentsInOneOrder` enforces one-order ownership.                                               |
| 7      | Valid payment subtyping                      | Conversions `cash2Pay`/`cred2pay`; not enforced if Payment constructor is exposed.                               | Structural subtyping via signature hierarchy; optional reinforcing check.                             |
| 8      | Status well-formed                           | `Status` datatype and `status : Status` in `Order`.                                                              | `enum Status` and field typing; check `ValidStatus`.                                                  |
| 9      | Operations (status, customer, total cost, …) | Selectors; executable `getCost`; customer equality and `query`; interface `IsOrder` with `costᵒ` and `queryᵒ`.   | Declarative assertions; no execution; could assert relationships involving costs if modeled.          |
| 10     | Verification modality                        | Type-level guarantees, reflection lemmas, and potential proofs over a System wrapper.                            | Facts and `check` for bounded counterexample search; `run` to generate instances.                     |

## Reasons for Differences

- Paradigm. Agda uses dependent types and constructive proofs; Alloy uses relational logic and SAT-based bounded checking.
- Ownership and Subtyping. Alloy naturally models ownership and subtyping via relations and signature hierarchies; Agda needs indexed types or restricted constructors to enforce them.
- Executability. Agda provides executable functions (e.g., `getCost`); Alloy is declarative and excels at global invariant checking and instance exploration.

## Conclusion

Both models satisfy the core specifications through their respective idioms:

- Alloy emphasizes global structural constraints (uniqueness, ownership, multiplicities) with automated bounded verification and instance generation.
- Agda encodes essential constraints in types (non-empty collections, status), offers executable operations with proofs, and can scale to stronger guarantees with a System wrapper.
