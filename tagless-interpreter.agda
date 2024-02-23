module tagless-interpreter where

open import Data.Nat
open import Data.Product

record Core (Exp : Set -> Set -> Set) : Set₁ where
  field
    int : ∀ {H : Set} -> ℕ -> Exp H ℕ
    add : ∀ {H : Set} -> Exp H ℕ -> Exp H ℕ -> Exp H ℕ
    z : ∀ {A H : Set} -> Exp (A × H) A
    s : ∀ {A B H : Set} -> Exp H A -> Exp (B × H) A
    l : ∀ {A B H : Set} -> Exp (A × H) B -> Exp H (A -> B)
    a : ∀ {A B H : Set} -> Exp H (A -> B) -> Exp H A -> Exp H B

data Exp : Set -> Set -> Set where
    ev : ∀ {A H : Set} -> (H -> A) -> Exp H A

getEv : ∀ {A H : Set} -> (Exp H A) -> (H -> A)
getEv (ev e) = e

expAsCore : Core Exp
expAsCore = record {
    int = (λ i -> ev ((λ h -> i)));
    add = (λ e1 e2 -> ev (λ h -> ((getEv e1) h) + ((getEv e2) h)));
    z = ev (λ ah -> proj₁ ah);
    s = (λ eah -> ev (λ bh -> (getEv eah) (proj₂ bh)));
    l = (λ eahb -> ev (λ h -> (λ a -> (getEv eahb) (a , h))));
    a = (λ eha2b eha -> ev (λ h -> ((getEv eha2b) h) ((getEv eha) h)))
    }

eval : ∀ {H A : Set} -> Exp H A -> H -> A
eval e h = (getEv e) h 