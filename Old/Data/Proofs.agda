module Data.Proofs{ℓₗ} where

import      Lvl
open import Data
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs{ℓₗ}
open import Sets.Setoid{ℓₗ} renaming (_≡_ to _≡ₛ_)
open import Type
open import Type.Empty

instance
  -- `Empty` is an empty type.
  Empty-IsEmpty : ∀{ℓ₁ ℓ₂} → IsEmpty{ℓ₁}{ℓ₂}(Empty)
  Empty-IsEmpty = IsEmpty.intro(empty)
