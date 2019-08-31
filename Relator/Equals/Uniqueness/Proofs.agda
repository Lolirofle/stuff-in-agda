module Relator.Equals.Uniqueness.Proofs where

import      Lvl
open import Functional
open import Logic.Propositional
open import Logic.Predicate
open import Relator.Equals
open import Relator.Equals.Uniqueness
open import Relator.Equals.Proofs
open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Type

-- TODO: This proof should work more generally for setoids when `Injective` is working for setoids
Uniqueness-Injectivity : ∀{A : Type{ℓ₂}}{B : Type{ℓ₂}}{f : A → B} → (∀{y : B} → Unique{A} (x ↦ y ≡ f(x))) ↔ Injective(f)
Uniqueness-Injectivity {A}{B} {f} = [↔]-intro l r where
  l : (∀{y : B} → Unique{A} (x ↦ y ≡ f(x))) ← Injective(f)
  l (injective) {y} {x₁}{x₂} (y≡fx₁) (y≡fx₂) = injective {x₁}{x₂} (symmetry(y≡fx₁) 🝖 (y≡fx₂))

  r : (∀{y : B} → Unique{A} (x ↦ y ≡ f(x))) → Injective(f)
  r (unique) {x₁}{x₂} (fx₁≡fx₂) = unique {f(x₁)}{x₁}{x₂} ([≡]-intro) (fx₁≡fx₂)
