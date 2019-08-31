module Type.Unit.Proofs where

open import Data
import      Lvl
open import Type.Empty
open import Type.Unit
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Relator.Properties

instance
  unit-is-pos : ∀{ℓ}{T : Set(ℓ)} → ⦃ _ : IsUnit(T) ⦄ → ◊(T)
  unit-is-pos ⦃ intro unit uniqueness ⦄ = intro ⦃ unit ⦄

instance
  unit-is-prop : ∀{ℓ}{T : Set(ℓ)} → ⦃ _ : IsUnit(T) ⦄ → IsProp(T)
  unit-is-prop {ℓ₁}{ℓ₂} ⦃ intro unit uniqueness ⦄ = intro (\{x}{y} → transitivity(_≡_) (uniqueness{x}) (symmetry(_≡_)(uniqueness{y}))) where

instance
  pos-prop-is-unit : ∀{ℓ}{T : Set(ℓ)} → ⦃ _ : (◊ T) ⦄ → ⦃ _ : IsProp(T) ⦄ → IsUnit(T)
  pos-prop-is-unit {ℓ} ⦃ intro ⦃ unit ⦄ ⦄ ⦃ intro uniqueness ⦄ = intro unit (\{x} → uniqueness{x}{unit}) where
