module Calculator where

open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.Float using (Float)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_; _×_)


data Primitive : Set where
  TEXT REAL INTEGER BOOLEAN : Primitive

data Type : Set where
  PrimTy    : Primitive → Type
  VectorTy  : ℕ → Type → Type

data SymbolKind : Set where
  INPUT INTERMEDIATE OUTPUT : SymbolKind

data Ctx : Set where
  ∅     : Ctx
  _▸_   : Ctx → (String × Type) → Ctx

data Env : Ctx → Set where
  empty : Env ∅
  extend : ∀ {Γ τ s} → Env Γ → (Γ ▸ (s , τ)) → Env (Γ ▸ (s , τ))

data _∈_ : Ctx → Type → Set where
  here  : ∀ {Γ τ s} → (Γ ▸ (s , τ)) ∈ τ
  there : ∀ {Γ τ σ} → Γ ∈ τ → (Γ ▸ σ) ∈ τ

data _⊢_ (Γ : Ctx) : Type → Set where
  text    : String → Γ ⊢ PrimTy TEXT
  real    : Float → Γ ⊢ PrimTy REAL
  int     : ℤ → Γ ⊢ PrimTy INTEGER
  bool    : Bool → Γ ⊢ PrimTy BOOLEAN
  
  var     : ∀ {τ} → Γ ∈ τ → Γ ⊢ τ
  
  ¬_      : Γ ⊢ PrimTy BOOLEAN → Γ ⊢ PrimTy BOOLEAN
  -_      : Γ ⊢ PrimTy REAL → Γ ⊢ PrimTy REAL
  
  _+_     : Γ ⊢ PrimTy REAL → Γ ⊢ PrimTy REAL → Γ ⊢ PrimTy REAL
  _*_     : Γ ⊢ PrimTy REAL → Γ ⊢ PrimTy REAL → Γ ⊢ PrimTy REAL
  _<_     : Γ ⊢ PrimTy REAL → Γ ⊢ PrimTy REAL → Γ ⊢ PrimTy BOOLEAN
  _∧_     : Γ ⊢ PrimTy BOOLEAN → Γ ⊢ PrimTy BOOLEAN → Γ ⊢ PrimTy BOOLEAN
  
  if_then_else_ : ∀ {τ} → Γ ⊢ PrimTy BOOLEAN → Γ ⊢ τ → Γ ⊢ τ → Γ ⊢ τ

data CalculationStep (Γ : Ctx) : Set where
  assign : ∀ {τ} → Γ ∈ τ → Γ ⊢ τ → CalculationStep Γ
  print  : String → ∀ {τ} → Γ ∈ τ → CalculationStep Γ

record SymbolDecl (Γ : Ctx) : Set where
  constructor symbolDecl
  field
    kind      : SymbolKind
    name      : String
    type      : Type

record TestCase (Γ : Ctx) : Set where
  constructor testCase
  field
    name        : String
    assignments : List (Σ Type λ τ → Γ ∈ τ × Γ ⊢ τ)
    assertions  : List (Γ ⊢ PrimTy BOOLEAN)

record Calculator : Set₁ where
  constructor calculator
  field
    name        : String
    ctx         : Ctx
    symbols     : List (SymbolDecl ctx)
    steps       : List (CalculationStep ctx)
    testCases   : List (TestCase ctx)

example : Calculator
example = record
  { name = "Sample Calculator"
  ; ctx = ∅ ▸ ("x" , PrimTy REAL)
  ; symbols = symbolDecl INPUT "x" (PrimTy REAL) ∷ []
  ; steps = assign here (real 3.14) ∷ print "Result: " here ∷ []
  ; testCases = testCase "Test1" [] (bool true ∷ []) ∷ []
  }