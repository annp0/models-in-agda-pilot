```agda
module OrderSystem where

open import Data.Float 
open import Data.String using (String)
open import Data.List using (List; []; _∷_; foldr)
open import Data.List.NonEmpty using (List⁺)
open import Data.Bool
open import Data.Product
open import Data.Nat using (ℕ; compare; Ordering; equal)
```

# OrderSystem

An order system consists of the following classes:

- `Order`, which stores the status of the order, 
    a list of `Item`s contained in the `Order`,
    and a list of `Payment`s.
    It must be owned by a `Customer`.
    It has a method to calculate the total cost of the order.
- `Customer`, which has a name, and could have multiple orders.
- `Item`, which has a name, and a cost.
- `Payment`, which could be `Cash` or `Credit`
    It stores the amount of the payment.
    It must be owned by an `Order`.

# The approach with specific data types

```agda
record Payment : Set
record Order : Set
record Customer : Set
record Item : Set
record Cash : Set
record Credit : Set

record Customer where
    field
        id : ℕ

record Order where
    field
        status : String
        customer : Customer
        items : List⁺ Item 
        payments : List⁺ Payment 

record Item where
    field
        name : String
        cost : Float

record Payment where
    field
        amount : Float

record Cash where
    field
        amount : Float

record Credit where
    field
        amount : Float
```

We can query the orders of a customer from a list of orders (`query`).

First, we need to establish the notion of equality on customers, by
comparing their ID.

```agda
compare-customer : Customer → Customer → Bool
compare-customer c1 c2 with (compare (Customer.id c1) (Customer.id c2)) 
...                        | (equal _) = true
...                        |  _        = false

query : List Order → Customer → List Order
query [] _ = []
query (o ∷ os) c = if compare-customer (Order.customer o) c 
                   then o ∷ (query os c) 
                   else (query os c)  
```

Payment could be formed from `Cash` or `Credit`.

```agda
cash2Pay : Cash → Payment
cash2Pay cash = record {amount = (Cash.amount cash)}

cred2pay : Credit → Payment
cred2pay credit = record {amount = (Credit.amount credit)}
```

To calculate the total cost for an order:

```agda
sum⁺ : List⁺ Item → Float
sum⁺ l⁺ = (Item.cost (List⁺.head l⁺)) + (foldr (λ item float → ((Item.cost item) + float))
                                       0.0 (List⁺.tail l⁺))

getCost : Order → Float
getCost o = sum⁺ (Order.items o)
```

# The pure API approach

With this approach, we could have a wide range of data types, 
and to see them as orders, we would need to implement the functions
as stated in the record `IsOrder`.

```agda
data Status : Set where
    success : Status
    failure : Status

record IsOrder (A : Set) : Set where
    field
        status : A → Status
        owner : A → Customer
        items : A → List⁺ Item
        payments : A → List⁺ Payment
```

`Listᵒ` is for storing a list of data that have the `IsOrder` predicate.
Since we are quantifying over all the sets, it needs to be `Set₁`.

Also we need store the data with the evidence that it is an order.

```agda
data Listᵒ : Set₁ where
    nil : Listᵒ
    con : ∀ {A : Set} → A × IsOrder A → Listᵒ → Listᵒ
```

For querying the orders that a customer has from a list

```agda
queryᵒ : Listᵒ → Customer → Listᵒ
queryᵒ nil c = nil
queryᵒ (con (a , eva) os) c = if (compare-customer c ((IsOrder.owner eva) a))
                              then con (a , eva) (queryᵒ os c)
                              else (queryᵒ os c) 
```

For computing the cost of an order

```agda
costᵒ : ∀ {A : Set} → A → IsOrder A → Float
costᵒ a eva = sum⁺ ((IsOrder.items eva) a)
```