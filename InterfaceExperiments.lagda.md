```agda
{-# OPTIONS --guardedness #-}
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.Nat
open import Data.Maybe
open import Data.Bool
open import Interface
open Interface.Interface
open Object
```

# Example: A simple counter

```agda
data CounterInstr : Set where
    incr : CounterInstr
    decr : CounterInstr
    read : CounterInstr

data Status : Set where
    success : Status
    failure : Status

Counter : Interface
Counter .Question = CounterInstr
Counter .Answer incr = Status
Counter .Answer decr = Status
Counter .Answer read = ℕ

counter : ℕ → Object Counter
counter n .call incr = (success , counter (suc n))
counter n .call decr = (success , counter (pred n)) 
counter n .call read = (n , counter n)

test : Answers _ _
test = observe (incr ∷ incr ∷ decr ∷ read ∷ []) (counter 0)
```

The normalizing form of test should be `success ∷ (success ∷ (success ∷ (1 ∷ [])))`

# Example : Non-Repeating Lists

This example implements non-repeating lists (sequences) as interfaces.

```agda
data Seq : Set where
    nil : Seq
    con : ℕ → Seq → Seq

data SeqQs : Set where
    addQ : ℕ → SeqQs
    remQ : ℕ → SeqQs
    read : SeqQs

SeqI : Interface
SeqI .Question = SeqQs
SeqI .Answer (addQ _) = Status
SeqI .Answer (remQ _) = Status
SeqI .Answer (read) = Seq
```

The questions you can ask to `SeqI`:
- `addQ`: add a number to the end of the sequence. Will fail if the number
is already present in the sequence
- `remQ`: remove a number from the sequence. Will fail if the number
is not present in the sequence
- `read`: read out the sequence

```agda
eq? : ℕ → ℕ → Bool
eq? zero zero = true
eq? zero (suc _) = false
eq? (suc _) zero = false
eq? (suc m) (suc n) = eq? m n

in? : ℕ → Seq → Bool
in? m nil = false
in? m (con n ns) with eq? m n
...                 | true = true
...                 | false = in? m ns
```

`eq?` compares two integers, while `in?` judges whether a number
is present in a sequence

```agda
add : ℕ → Seq → Status × Seq
add n s = if (in? n s) then (failure , s) else (success , (con n s))

remove : ℕ → Seq → Status × Seq
remove m nil = (failure , nil)
remove m (con n ns) with eq? m n
...                     | true = (success , ns)
...                     | false = let rs = (remove m ns) 
                                in (proj₁ rs , con n (proj₂ rs))

seq : Seq → Object SeqI
seq s .call (addQ m) = let rs = add m s in (proj₁ rs , seq (proj₂ rs))
seq s .call (remQ m) = let rs = remove m s in (proj₁ rs , seq (proj₂ rs))
seq s .call (read) = (s , seq s)
```

`add` and `remove` performs the actual task and wraps the status and value together.
This simplified the implementation of the object function.

```agda
testSeq : Answers _ _
testSeq = observe ((addQ 1) ∷ (addQ 3) ∷ (addQ 4) ∷ (remQ 2) ∷ (addQ 3) ∷ (remQ 1) ∷ (read) ∷ []) (seq nil)
```

The normal form of `testSeq` is 
```plain
success ∷ (success ∷ (success ∷ (failure ∷ (failure ∷ (success ∷ 
(con 4 (con 3 nil) ∷ []))))))
``` 