module order-system-example where

open import Data.Float using (Float)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; foldr)

open import order-system

alice : Customer
alice = info "Alice" "Wonderland"

hat : Item
hat = info 2.0 "Mad Hatter Co. Ltd"

orderdetail : OrderDetail
orderdetail = info 3.0 "HST/GST" hat

cash : Cash
cash = info 35.00

payment : Payment
payment = fromCash cash

order : Order
order = info "FEB 30" "Shipping" alice (head payment) (orderdetail ∷ [])
