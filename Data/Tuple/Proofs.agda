module Data.Tuple.Proofs where

import      Lvl
open import Data using (Unit ; <>)
open import Data.Tuple using (_⨯_ ; _,_)
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs
open import Type

Tuple-equality : ∀{ℓₒ₁ ℓₒ₂}{T₁ : Type{ℓₒ₁}}{T₂ : Type{ℓₒ₂}}{x₁ y₁ : T₁}{x₂ y₂ : T₂} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → ((x₁ , x₂) ≡ (y₁ , y₂))
Tuple-equality [≡]-intro [≡]-intro = [≡]-intro
