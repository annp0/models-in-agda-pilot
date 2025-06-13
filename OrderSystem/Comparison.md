## Model Specifications

### Entities

1. Customer
   - Has a unique identifier

2. Item
   - Has a name/description
   - Has an associated cost value

3. Payment
   - Abstract concept with two concrete types:
     - Cash payment
     - Credit payment
   - Has an amount

4. Order
   - Has a status (success or failure)
   - References exactly one customer
   - Contains a non-empty collection of items
   - Contains a non-empty collection of payments

### Relationships

- Each order is associated with exactly one customer
- Each order contains one or more items
- Each order has one or more payments
- Each payment belongs to exactly one order

### Constraints

- Customer identifiers must be unique within the system
- Orders must have at least one item
- Orders must have at least one payment
- All referenced customers must exist in the system
- All payments must be of a valid subtype (Cash or Credit)

### Operations

- Ability to determine order status
- Ability to identify the customer for a given order
- Ability to calculate the total cost of an order
- Ability to verify payment validity

## Alloy Model 

Alloy models an order processing system with:

- Customer: Signatures with unique positive integer IDs
- Item: Signatures with name (String) and cost (Int) 
- Payment: Abstract signature with concrete subtypes Cash and Credit
- Order: Contains status, customer reference, items, and payments
- Status: Enumeration with success/failure values

Key constraints:
- Customer IDs must be unique (enforced via fact)
- Each payment belongs to exactly one order
- Orders must have at least one item and payment (via 'some' multiplicity)

The model includes verification checks to ensure all orders have valid status, referenced customers exist, no empty collections, and payments are valid subtypes.

### Agda Model (OrderSystem.lagda.md)

The Agda implementation offers two modeling approaches:

1. With Specific Data Types:
   - Defines concrete record types for all entities
   - Customer with natural number ID
   - Item with name and floating-point cost
   - Payment, Cash, and Credit with amount fields
   - Order with status, customer, non-empty lists of items and payments

2. Pure API Approach:
   - Defines an interface `IsOrder` that abstracts the order concept
   - Any type can implement this interface to be treated as an order
   - Operations defined in terms of the interface rather than concrete types

The implementation includes:
- Customer equality checking with proofs
- Order querying by customer
- Payment type conversion (Cash/Credit to Payment)
- Cost calculation functionality

## Comparison of Models

### Type System

- Alloy: Lightweight type system based on sets and relations
- Agda: Dependent type system with stronger static guarantees
  - Uses `List⁺` (non-empty lists) to guarantee orders have items/payments
  - Provides type-level guarantees that Alloy enforces through facts

### Constraint Enforcement

- Alloy: Uses explicit facts and multiplicity constraints 
  - `uniqueCustomerIds` fact ensures ID uniqueness
  - `paymentsInOneOrder` fact ensures payment ownership
- Agda: Type-level constraints (e.g. Non-emptiness through specialized types, and proposition as equality types)

### Verification

- Alloy: Model checking through counterexample generation
- Agda: Type checking with constructive proofs of properties

### Reason

The differences in the implementations stem primarily from language-specific design forces:

- Alloy:
  - The language by nature forces a focus on relations and constraints rather than computation
  - Its signature system requires explicit facts to enforce model properties
  - Encourages verification through counterexample generation
  - Limited computational expressivity means the focus is on structural properties, not executable behavior

- Agda:
  - Dependent type system enables encoding constraints directly in types (e.g., non-empty lists)
  - The Curry-howard correspondance allows formal verification of properties through constructive proofs

#### Implementation Consequences

These language constraints result in fundamentally different artifacts:
- Alloy produces a specification that can be analyzed but not executed
- Agda produces executable code with formal guarantees
- Alloy verifies through bounded checking of constraint satisfaction
- Agda verifies through type checking and proof construction
- Alloy expresses constraints explicitly as logical formulas
- Agda encodes many constraints implicitly in its type definitions

