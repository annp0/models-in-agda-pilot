module OrderSystem

-- Customers have unique IDs
sig Customer {
    id: Int
} {
    id > 0  -- Assuming positive IDs
}

-- Ensure all customer IDs are unique
fact uniqueCustomerIds {
    no disj c1, c2: Customer | c1.id = c2.id
}

-- Items have a name and cost
sig Item {
    name: String,
    cost: Int
}

-- Payments can be Cash or Credit, each with an amount
abstract sig Payment {
    amount: Int
}
sig Cash extends Payment {}
sig Credit extends Payment {}

-- Orders have a status, customer, items, and payments
sig Order {
    status: Status,
    customer: Customer,
    items: some Item,       -- At least one item
    payments: some Payment  -- At least one payment
}

-- Order status can be success or failure
enum Status { success, failure }

-- Each payment belongs to exactly one order
fact paymentsInOneOrder {
    all p: Payment | one o: Order | p in o.payments
}

-- Example checks to validate model properties

-- Every order has a valid status
check ValidStatus {
    all o: Order | o.status in Status
}

-- All customers in orders exist
check CustomersExist {
    all o: Order | o.customer in Customer
}

-- No order can have empty items or payments
check NonEmptyItemsPayments {
    all o: Order | some o.items and some o.payments
}

-- Payments must be either Cash or Credit
check PaymentSubtypes {
    all p: Payment | p in Cash or p in Credit
}

-- Run command to generate instances
run {} for 5 but 3 Int
