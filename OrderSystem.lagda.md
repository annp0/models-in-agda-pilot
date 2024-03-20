```
module OrderSystem where

open import Data.Float using (Float; _*_; _+_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Bool
open import Data.Nat
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

```
data NonEmptyList (A : Set) : Set where
    nil : A → NonEmptyList A
    con : A → NonEmptyList A → NonEmptyList A
```

```
data Payment : Set
data Order : Set
data Customer : Set
data Item : Set
data Cash : Set
data Credit : Set

data Customer where
    info : ℕ → Customer
    -- id

data Order where
    info : String → Customer → NonEmptyList Item → NonEmptyList Payment → Order 
    -- status, list of items, list of payments

data Item where
    info : String → Float → Item
    -- name, cost

data Payment where
    info : Float → Payment
    -- amount

data Cash where
    info : Float → Cash
    -- amount

data Credit where
    info : Float → Credit
    -- amount
```

We can query the orders of a customer from a list of orders (`query`).

First, we need to establish the notion of equality on customers, by
comparing their ID.

```
eq? : ℕ → ℕ → Bool
eq? zero zero = true
eq? zero (suc _) = false
eq? (suc _) zero = false
eq? (suc m) (suc n) = eq? m n

eqc? : Customer → Customer → Bool
eqc? (info n1) (info n2) = if (eq? n1 n2) then true else false

query : List Order → Customer → List Order
query [] _ = []
query ((info i1 oc i2 i3) ∷ os) c = if eqc? oc c then (info i1 oc i2 i3) ∷ (query os c) else (query os c)  
```

Payment could be formed from `Cash` or `Credit`.

```
cash2Pay : Cash → Payment
cash2Pay (info n) = info n

cred2pay : Credit → Payment
cred2pay (info n) = info n
```

To calculate the total cost for an order:

```
sum : NonEmptyList Item → Float
sum (nil (info _ c)) = c
sum (con (info _ c) is) = Data.Float._+_ c (sum is)

getCost : Order → Float
getCost (info _ _ is _) = sum is
```