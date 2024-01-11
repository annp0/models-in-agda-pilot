module order-system where

open import Data.Float using (Float; _*_; _+_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; foldr)

data Payment : Set
data Order : Set
data Customer : Set
data OrderDetail : Set
data Item : Set

data NEList (A : Set) : Set where
    -- the non-empty list
    head :  A → NEList A
    succ :  A → NEList A → NEList A

data Customer where
    info : String → String → Customer
    -- name, address, list of orders

data Order where
    info : String → String → Customer → NEList Payment → List OrderDetail → Order
    -- date, status, customer, non-empty list of payments

data OrderDetail where
    info : Float → String → Item → OrderDetail
    -- quantity, taxStatus, the item 

data Item where
    info : Float → String → Item
    -- shippingWeight, description

data Cash : Set where
    info : Float → Cash
    -- cashTendered

data Check : Set where
    info : String → String → Bool → Check
    -- name, bankID, authorized

data Credit : Set where
    info : String → String → String → Bool → Credit
    -- number, type, expDate, authorized

data Payment where
    fromCash : Cash → Payment
    fromCheck : Check → Payment
    fromCredit : Credit → Payment

getPriceForItem : Item → Float
getPriceForItem item = 1.0

getPriceForOD : OrderDetail → Float
getPriceForOD (info num _ item) = (getPriceForItem item) * num

getPriceForOrder : Order → Float
getPriceForOrder (info _ _ _ _ lOD) = foldr (λ OD x → x + (getPriceForOD OD)) 0.0 lOD

inStock : Item → Bool
inStock item = true
