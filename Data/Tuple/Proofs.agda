module Data.Tuple.Proofs where

import      Lvl
open import Data using (Unit ; <>)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs
open import Type

private variable ℓ ℓₒ₁ ℓₒ₂ : Lvl.Level
private variable A B : Type{ℓ}
private variable f g : A → B
private variable p : A ⨯ B

Tuple-equality : ∀{x₁ y₁ : A}{x₂ y₂ : B} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → ((x₁ , x₂) ≡ (y₁ , y₂))
Tuple-equality [≡]-intro [≡]-intro = [≡]-intro

Tuple-left-map : (Tuple.right(Tuple.map f g p) ≡ g(Tuple.right(p)))
Tuple-left-map = [≡]-intro

Tuple-right-map : (Tuple.right(Tuple.map f g p) ≡ g(Tuple.right(p)))
Tuple-right-map = [≡]-intro
