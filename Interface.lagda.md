```agda
{-# OPTIONS --guardedness #-}
module Interface where

open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
```

# Interfaces

An interface defines the range of questions you can ask and 
the range of answers you would expect for each question.

```agda
record Interface : Set₁ where
    field
        Question : Set
        Answer : Question → Set

open Interface
```

⊗ lets you construct a new interface by asking two questions and expecting two answers.

```agda
_⊗_ : Interface → Interface → Interface
(I ⊗ J) .Question = I .Question × J .Question
(I ⊗ J) .Answer (i , j) = I .Answer i × J .Answer j

```

⊕ is similar.

```agda
_⊕_ : Interface → Interface → Interface
(I ⊕ J) .Question = I .Question ⊎ J .Question
(I ⊕ J) .Answer (inj₁ i) = I .Answer i
(I ⊕ J) .Answer (inj₂ j) = J .Answer j
```

♭ lets you construct an interface by asking two questions in a sequence.

```agda
_♭_ : Interface → Interface → Interface
(I ♭ J) .Question = Σ[ i ∈ I .Question ] (I .Answer i → J .Question)
(I ♭ J) .Answer (i , next) = Σ[ i' ∈ I .Answer i ] (J .Answer (next i'))
```

⇒ is the morphism between interfaces.

```agda
record _>_ (P Q : Interface) : Set where
    field
        ask : P .Question → Q .Question
        answer : (p : P .Question) → Q .Answer (ask p) → P .Answer p
```

An object can be called with a question, it will answer the question and return 
a new object with possible state change

```agda
record Object (I : Interface) : Set where
    coinductive
    field
        call : ∀ (i : I .Question) → I .Answer i × Object I

open Object
```

The following is just for storing answers and getting the sequence started.

```agda
data Answers (I : Interface) : List (I .Question) → Set where
    [] : Answers I []
    _∷_ : ∀ {q : I .Question} {qs : List (I .Question)} → I .Answer q → Answers I qs → Answers I (q ∷ qs)

observe : {I : Interface} → (qs : List (I .Question)) → Object I → Answers I qs
observe [] obj = []
observe (q ∷ qs) obj = let (answer , obj') = (obj .call q) in answer ∷ (observe qs obj')
```