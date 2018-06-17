module Data.Boolean.AsSet where

open import Data.Boolean
open import Functional
open import Functional.DomainRaise
open import Logic.Propositional

-- BoolIsTrue : ∀{ℓ₁ ℓ₂}{n}{X : Set(ℓ₁)} → (X →̂ Bool)(n) → (X →̂ Set(ℓ₂))(n)
-- BoolIsTrue(f) = (if_then ⊤ else ⊥) [∘] f

BoolIsTrue : ∀{ℓ} → Bool → Set(ℓ)
BoolIsTrue = if_then ⊤ else ⊥

BoolFnIsTrue : ∀{ℓ₁ ℓ₂}{X : Set(ℓ₁)} → (X → Bool) → (X → Set(ℓ₂))
BoolFnIsTrue = BoolIsTrue ∘_
