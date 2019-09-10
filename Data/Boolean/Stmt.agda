module Data.Boolean.Stmt where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Functional
open import Logic.Propositional

-- IsTrue : ∀{ℓ₁ ℓ₂}{n}{X : Set(ℓ₁)} → (X →̂ Bool)(n) → (X →̂ Set(ℓ₂))(n)
-- IsTrue(f) = (if_then ⊤ else ⊥) [∘] f

IsTrue : Bool → Set(Lvl.𝟎)
IsTrue = if_then ⊤ else ⊥

FnIsTrue : ∀{ℓ}{X : Set(ℓ)} → (X → Bool) → (X → Set(Lvl.𝟎))
FnIsTrue = IsTrue ∘_

IsFalse : Bool → Set(Lvl.𝟎)
IsFalse = IsTrue ∘ !_

FnIsFalse : ∀{ℓ}{X : Set(ℓ)} → (X → Bool) → (X → Set(Lvl.𝟎))
FnIsFalse = IsFalse ∘_
