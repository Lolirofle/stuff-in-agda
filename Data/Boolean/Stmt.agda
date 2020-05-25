module Data.Boolean.Stmt where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Functional
open import Logic.Propositional
open import Type

-- IsTrue : ∀{ℓ₁ ℓ₂}{n}{X : Set(ℓ₁)} → (X →̂ Bool)(n) → (X →̂ Set(ℓ₂))(n)
-- IsTrue(f) = (if_then ⊤ else ⊥) [∘] f

IsTrue : Bool → Type{Lvl.𝟎}
IsTrue = if_then ⊤ else ⊥

IsFalse : Bool → Type{Lvl.𝟎}
IsFalse = IsTrue ∘ !
