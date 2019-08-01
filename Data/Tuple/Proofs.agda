module Data.Tuple.Proofs{ℓₗ} where

import      Lvl
open import Data using (Unit ; <>)
open import Data.Tuple using (_⨯_ ; _,_)
open import Logic.Propositional
open import Relator.Equals{ℓₗ}
open import Relator.Equals.Proofs{ℓₗ}
open import Type

Tuple-equality : ∀{ℓₒ₁ ℓₒ₂}{T₁ : Type{ℓₒ₁}}{T₂ : Type{ℓₒ₂}}{x₁ y₁ : T₁}{x₂ y₂ : T₂} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → ((x₁ , x₂) ≡ (y₁ , y₂))
Tuple-equality [≡]-intro [≡]-intro = [≡]-intro
