```
module OrderSystem where

open import Data.Float using (Float; _*_; _+_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; foldr)
```

# OrderSystem

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

# ToDo

Ensure every order must have a customer, and every payment has an order.

In fact, this is the same problem with trees - how to model ownership?

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
    info : String → List Order → Customer
    -- name, list of orders

data Order where
    info : String → NonEmptyList Item → NonEmptyList Payment → Order 
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
sum (con (info _ c) is) = c + (sum is)
```

```
getCost : Order → Float
getCost (info _ is _) = sum is
```