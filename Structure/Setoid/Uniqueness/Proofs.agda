module Structure.Setoid.Uniqueness.Proofs where

import      Lvl
open import Functional
open import Function.Names
open import Logic.Propositional
open import Logic.Predicate
open import Relator.Equals
open import Structure.Setoid.Uniqueness
open import Relator.Equals.Proofs
-- TODO: open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

module _ {ℓ₁ ℓ₂} {A : Type{ℓ₁}} {B : Type{ℓ₂}} {f : A → B} where
  -- TODO: This proof should work more generally for setoids when `Injective` is working for setoids
  Uniqueness-Injectivity : (∀{y : B} → Unique(x ↦ y ≡ f(x))) ↔ Injective(f)
  Uniqueness-Injectivity = [↔]-intro l r where
    l : (∀{y : B} → Unique(x ↦ y ≡ f(x))) ← Injective(f)
    l (injective) {y} {x₁}{x₂} (y≡fx₁) (y≡fx₂) = injective {x₁}{x₂} (symmetry(_≡_) (y≡fx₁) 🝖 (y≡fx₂))

    r : (∀{y : B} → Unique(x ↦ y ≡ f(x))) → Injective(f)
    r (unique) {x₁}{x₂} (fx₁≡fx₂) = unique {f(x₁)}{x₁}{x₂} ([≡]-intro) (fx₁≡fx₂)
