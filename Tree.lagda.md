```
module Tree where

open import Data.Nat
open import Data.Bool
open import Data.List
```

# Trees

To model file systems, I think it will be better to start directly with trees.

The nodes of the tree is uniquely indexed by integers.

```
data Tree : Set where
    leaf : ℕ → Tree
    node : ℕ → List Tree → Tree
```

The function `eq?` compares two integers.

```
eq? : ℕ → ℕ → Bool
eq? zero zero = true
eq? zero (suc _) = false
eq? (suc _) zero = false
eq? (suc m) (suc n) = eq? m n
```

`in?` checks whether an integer is already present in a tree.

!! `in?` fails termination checking...

```
in? : ℕ → Tree → Bool
in? m (leaf n) = eq? m n
in? m (node n ns) = if (eq? m n) then true else 
                    (foldr _∨_ false (map (in? m) ns))
```