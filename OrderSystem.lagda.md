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
    eta-equality
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