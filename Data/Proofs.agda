module Data.Proofs where

import      Lvl
open import Data
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs
open import Sets.Setoid renaming (_≡_ to _≡ₛ_)
open import Type
open import Type.Empty

instance
  -- `Empty` is an empty type.
  Empty-IsEmpty : ∀{ℓ} → IsEmpty{ℓ}(Empty)
  Empty-IsEmpty = IsEmpty.intro(empty)
