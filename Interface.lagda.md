```
{-# OPTIONS --guardedness #-}
module Interface where

open import Data.Product
open import Data.Sum
open import Data.List
open import Data.Nat
```

# Interface

Experiments with interfaces

# Todo 

- Read on algebras and coalgebras
- Model binary trees with interfaces

# Interfaces

An interface defines the range of questions you can ask and 
the range of answers you would expect for each question.

```
record Interface : Set₁ where
    field
        Question : Set
        Answer : Question → Set

open Interface
```

⊗ lets you construct a new interface by asking two questions and expecting two answers.

```
_⊗_ : Interface → Interface → Interface
(I ⊗ J) .Question = I .Question × J .Question
(I ⊗ J) .Answer (i , j) = I .Answer i × J .Answer j

```

⊕ is similar.

```
_⊕_ : Interface → Interface → Interface
(I ⊕ J) .Question = I .Question ⊎ J .Question
(I ⊕ J) .Answer (inj₁ i) = I .Answer i
(I ⊕ J) .Answer (inj₂ j) = J .Answer j
```

♭ lets you construct an interface by asking two questions in a sequence.

```
_♭_ : Interface → Interface → Interface
(I ♭ J) .Question = Σ[ i ∈ I .Question ] (I .Answer i → J .Question)
(I ♭ J) .Answer (i , next) = Σ[ i' ∈ I .Answer i ] (J .Answer (next i'))
```

⇒ is the morphism between interfaces.

```
record _⇒_ (P Q : Interface) : Set where
    field
        ask : P .Question → Q .Question
        answer : (p : P .Question) → Q .Answer (ask p) → P .Answer p

open _⇒_
```

An object can be called with a question, it will answer the question and return 
a new object with possible state change

```
record Object (I : Interface) : Set where
    coinductive
    field
        call : ∀ (i : I .Question) → I .Answer i × Object I

open Object
```

The following is just for storing answers and getting the sequence started.

```
data Answers (I : Interface) : List (I .Question) → Set where
    [] : Answers I []
    _∷_ : ∀ {q : I .Question} {qs : List (I .Question)} → I .Answer q → Answers I qs → Answers I (q ∷ qs)

observe : {I : Interface} → (qs : List (I .Question)) → Object I → Answers I qs
observe [] obj = []
observe (q ∷ qs) obj = let (answer , obj') = (obj .call q) in answer ∷ (observe qs obj')
```

# Example

```
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