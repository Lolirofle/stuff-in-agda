module Structure.Setoid.Proofs where

import      Lvl
open import Structure.Setoid
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

module _ {ℓ ℓₑ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  instance
    [≡][≢]-subtransitivityₗ : Subtransitivityₗ(_≢_)(_≡_)
    [≡][≢]-subtransitivityₗ = intro(\ab nbc ac → nbc(symmetry(_≡_) ab 🝖 ac))

  instance
    [≡][≢]-subtransitivityᵣ : Subtransitivityᵣ(_≢_)(_≡_)
    [≡][≢]-subtransitivityᵣ = intro(\nab bc ac → nab(ac 🝖 symmetry(_≡_) bc))
