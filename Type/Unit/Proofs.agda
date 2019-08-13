module Type.Unit.Proofs where

open import Data
import      Lvl
open import Type.Empty
open import Type.Unit
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs
import      Structure.Relator.Properties

instance
  unit-is-pos : ∀{ℓ}{T : Set(ℓ)} → ⦃ _ : IsUnit{ℓ}(T) ⦄ → ◊{ℓ}(T)
  unit-is-pos ⦃ intro unit uniqueness ⦄ = intro ⦃ unit ⦄

instance
  unit-is-prop : ∀{ℓ₁ ℓ₂}{T : Set(ℓ₂)} → ⦃ _ : IsUnit{ℓ₁ Lvl.⊔ ℓ₂}{ℓ₂}(T) ⦄ → IsProp{ℓ₁ Lvl.⊔ ℓ₂}{ℓ₂}(T)
  unit-is-prop {ℓ₁}{ℓ₂} ⦃ intro unit uniqueness ⦄ = intro (\{x}{y} → transitivity (uniqueness{x}) (symmetry(uniqueness{y}))) where
    open Structure.Relator.Properties{ℓ₁}{ℓ₂}

instance
  pos-prop-is-unit : ∀{ℓ₁ ℓ₂}{T : Set(ℓ₂)} → ⦃ _ : (◊ T) ⦄ → ⦃ _ : IsProp{ℓ₁ Lvl.⊔ ℓ₂}{ℓ₂}(T) ⦄ → IsUnit{ℓ₁ Lvl.⊔ ℓ₂}{ℓ₂}(T)
  pos-prop-is-unit {ℓ₁}{ℓ₂} ⦃ intro ⦃ unit ⦄ ⦄ ⦃ intro uniqueness ⦄ = intro unit (\{x} → uniqueness{x}{unit}) where
    open Structure.Relator.Properties{ℓ₁}{ℓ₂}
