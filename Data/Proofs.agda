module Data.Proofs where

import      Lvl
open import Data
open import Logic.Propositional
open import Sets.Setoid renaming (_≡_ to _≡ₛ_)
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Type
open import Type.Empty

module _ {ℓ} where
  open import Relator.Equals renaming (_≡_ to _≡ₑ_)
  open import Relator.Equals.Proofs.Equivalence

  instance
    Empty-equiv : Equiv(Empty{ℓ})
    Empty-equiv = [≡]-equiv

instance
  -- `Empty` is an empty type.
  Empty-IsEmpty : ∀{ℓ} → IsEmpty{ℓ}(Empty)
  Empty-IsEmpty = IsEmpty.intro(empty)

module _ {ℓ₁ ℓ₂} {T : Type{ℓ₁}} ⦃ _ : Equiv(T) ⦄ where
  instance
    empty-injective : Injective(empty{ℓ₁}{ℓ₂}{T})
    Injective.proof(empty-injective) {}
