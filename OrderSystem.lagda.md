```agda
module OrderSystem where

open import Data.Float 
open import Data.String using (String)
open import Data.List using (List; []; _∷_; foldr; filter)
open import Data.List.NonEmpty using (List⁺)
open import Data.Bool
open import Data.Product
open import Data.Nat using (ℕ; compare; Ordering; equal)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

import Data.Nat as Nat
import Data.Nat.Properties as Natₚ
```

# OrderSystem

## Informal Specification

An order system consists of the following classes:

- `Order`, which stores the status of the order, 
    a non-empty list of `Item`s contained in the `Order`,
    and a non-empty list of `Payment`s.
    It must be owned by a `Customer`.
    It has a method to calculate the total cost of the order.
- `Customer`, which has a name, and could have multiple orders.
- `Item`, which has a name, and a cost.
- `Payment`, which could be `Cash` or `Credit`
    It stores the amount of the payment.
    It must be owned by an `Order`.

## By-signature Specification

- `Customer : Set` should be a record with a single field `id : ℕ`
- `Cash : Set` and `Credit : Set` should be a record containing
    a field `amount : Float` and other status information 
- `Payment : Set` a record that contains a single field `amount : Float`
    can be formed from `Cash` or `Credit` by respective functions
    `cash2Pay : Cash → Payment` and `cred2Pay : Credit → Payment`
- `Order : Set` should be a record with the following fields:
    a non-empty list of items `items : List⁺ Item`
    a non-empty list of payments `payments : List⁺ Payment`
    a customer `Customer`
    the current `Status : Set`
    and a function that returns its total cost `cost : Order → Float`

# The approach with specific data types

```agda
data Status : Set where
    success : Status
    failure : Status

record Customer : Set where
    eta-equality
    field
        id : ℕ

record Item : Set where
    field
        name : String
        cost : Float

record Payment : Set where
    field
        amount : Float

record Cash : Set where
    field
        amount : Float

record Credit : Set where
    field
        amount : Float

record Order : Set where
    field
        status : Status
        customer : Customer
        items : List⁺ Item 
        payments : List⁺ Payment 
```

For customers, we need to define equality for them.

```agda
-- posible with eta-equality
customer-equal
  : ∀ {x y : Customer} 
  → Customer.id x ≡ Customer.id y 
  → x ≡ y
customer-equal refl = refl

-- a quick way of getting boolean values
customer-equal? : ∀ (x y : Customer) → Bool
customer-equal? x y = Customer.id x Nat.≡ᵇ Customer.id y

-- extract proof from the boolean result (true)
reflect-≡ᵇ : ∀ (x y : ℕ) → (x Nat.≡ᵇ y) ≡ true → x ≡ y
reflect-≡ᵇ Nat.zero Nat.zero p = refl
reflect-≡ᵇ (Nat.suc x) (Nat.suc y) p = cong Nat.suc (reflect-≡ᵇ x y p)

-- extract proof from the boolean result (false)
refute-≡ᵇ : ∀ (x y : ℕ) → (x Nat.≡ᵇ y) ≡ false → ¬ (x ≡ y)
refute-≡ᵇ Nat.zero Nat.zero () q
refute-≡ᵇ (Nat.suc x) (Nat.suc y) p q = 
    refute-≡ᵇ x y p (Natₚ.suc-injective q)

customer-equal-reflects 
  : ∀ (x y : Customer) 
  → Reflects (x ≡ y) (customer-equal? x y)
customer-equal-reflects x y with customer-equal? x y in p
    -- if false, give the proof that x≠y
... | false = ofⁿ (λ x=y → refute-≡ᵇ (Customer.id x) (Customer.id y) p (cong Customer.id x=y))
    -- if true, give the proof that x=y
... | true = ofʸ (customer-equal (reflect-≡ᵇ _ _ p))

customer-equal-dec : ∀ (x y : Customer) → Dec (x ≡ y)
customer-equal-dec x y = customer-equal? x y because customer-equal-reflects x y
```

We can query the orders of a customer from a list of orders (`query`).

```agda
query : List Order → Customer → List Order
query os c = filter (λ o → customer-equal-dec (Order.customer o) c) os 
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
-- handwrite this seemed more convenient than using stdlib
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
record IsOrder (A : Set) : Set where
    field
        status : A → Status
        owner : A → Customer
        items : A → List⁺ Item
        payments : A → List⁺ Payment
```

The type for a list of order is now

```agda
Listᵒ : Set₁
Listᵒ = List (Σ Set (λ A → A × IsOrder A))
```
For querying the orders that a customer has from a list

```agda
queryᵒ : Listᵒ → Customer → Listᵒ
queryᵒ os c = filter (λ (_ , (a , eva)) → 
            customer-equal-dec c ((IsOrder.owner eva) a)) os
```

For computing the cost of an order

```agda
costᵒ : ∀ {A : Set} → A → IsOrder A → Float
costᵒ a eva = sum⁺ ((IsOrder.items eva) a)
``` 