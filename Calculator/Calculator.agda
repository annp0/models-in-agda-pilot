module Calculator where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; foldr; filter; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Vec using (Vec)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
-- Using Float for Real
open import Data.Float using (Float) 
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Float using (_+_; _-_; _*_; _÷_)
open import Data.Bool using (_∧_; _∨_; not)

data PrimitiveType : Set where
  text real integer boolean : PrimitiveType

data Type : Set where
  base   : PrimitiveType → Type
  vector : Type → Type

record Symbol : Set where
  field
    name : String
    type : Type

data LiteralValue : Type → Set where
  textLit    : String → LiteralValue (base text)
  realLit    : Float → LiteralValue (base real)
  integerLit : ℕ → LiteralValue (base integer)
  booleanLit : Bool → LiteralValue (base boolean)

Entry : Set
Entry = Σ Symbol (λ s → LiteralValue (Symbol.type s))

Environment : Set
Environment = List Entry

data UnaryOp : Type → Type → Set where
  negate : UnaryOp (base real) (base real)
  flip    : UnaryOp (base boolean) (base boolean)

data BinaryOp : Type → Type → Type → Set where
  add      : BinaryOp (base real) (base real) (base real)
  subtract : BinaryOp (base real) (base real) (base real)
  multiply : BinaryOp (base real) (base real) (base real)
  divide   : BinaryOp (base real) (base real) (base real)

data Expression : Environment → Type → Set where
  literal      : ∀ {env typ} → LiteralValue typ → Expression env typ
  symbolRef    : ∀ {env} → (entry : Entry) → entry ∈ env → Expression env (Symbol.type (proj₁ entry))
  unaryExpr    : ∀ {env t₁ t₂} → UnaryOp t₁ t₂ → Expression env t₁ → Expression env t₂
  binaryExpr   : ∀ {env t₁ t₂ t₃} → BinaryOp t₁ t₂ t₃ → Expression env t₁ → Expression env t₂ → Expression env t₃
          
evalUnaryOp : ∀ {t₁ t₂} → UnaryOp t₁ t₂ → LiteralValue t₁ → LiteralValue t₂
evalUnaryOp negate (realLit x) = realLit (Data.Float.- x)
evalUnaryOp flip (booleanLit b) = booleanLit (Data.Bool.not b)

evalBinaryOp : ∀ {t₁ t₂ t₃} → BinaryOp t₁ t₂ t₃ → LiteralValue t₁ → LiteralValue t₂ → LiteralValue t₃
evalBinaryOp add (realLit x) (realLit y) = realLit (x + y)
evalBinaryOp subtract (realLit x) (realLit y) = realLit (x - y)
evalBinaryOp multiply (realLit x) (realLit y) = realLit (x * y)
evalBinaryOp divide (realLit x) (realLit y) = realLit (x ÷ y)

evaluate : ∀ {env typ} → Expression env typ → LiteralValue typ
evaluate (literal val) = val
evaluate (symbolRef entry _) = proj₂ entry
evaluate (unaryExpr op expr) = evalUnaryOp op (evaluate expr)
evaluate (binaryExpr op expr₁ expr₂) = evalBinaryOp op (evaluate expr₁) (evaluate expr₂)