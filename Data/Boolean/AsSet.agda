module Data.Boolean.AsSet where

open import Data.Boolean
open import Functional
open import Functional.DomainRaise
open import Logic.Propositional

-- boolToSet : ∀{ℓ₁ ℓ₂}{n}{X : Set(ℓ₁)} → (X →̂ Bool)(n) → (X →̂ Set(ℓ₂))(n)
-- boolToSet(f) = (if_then ⊤ else ⊥) [∘] f

boolToSet : ∀{ℓ} → Bool → Set(ℓ)
boolToSet = if_then ⊤ else ⊥

boolToSetFn : ∀{ℓ₁ ℓ₂}{X : Set(ℓ₁)} → (X → Bool) → (X → Set(ℓ₂))
boolToSetFn(f) = boolToSet ∘ f
