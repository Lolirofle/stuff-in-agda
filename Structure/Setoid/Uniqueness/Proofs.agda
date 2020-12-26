module Structure.Setoid.Uniqueness.Proofs where

import      Lvl
open import Functional
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid.Uniqueness
open import Structure.Setoid
open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable A B : Type{ℓ}
private variable P : A → Type{ℓ}

module _ ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ {f : A → B} where
  Uniqueness-Injectivity : (∀{y : B} → Unique(x ↦ y ≡ f(x))) ↔ Injective(f)
  Uniqueness-Injectivity = [↔]-intro l r where
    l : (∀{y : B} → Unique(x ↦ y ≡ f(x))) ← Injective(f)
    l inj {y} {x₁}{x₂} (y≡fx₁) (y≡fx₂) = injective _ ⦃ inj ⦄ {x₁}{x₂} (symmetry(_≡_) (y≡fx₁) 🝖 (y≡fx₂))

    r : (∀{y : B} → Unique(x ↦ y ≡ f(x))) → Injective(f)
    Injective.proof(r unique) {x₁}{x₂} (fx₁≡fx₂) = unique {f(x₁)}{x₁}{x₂} (reflexivity(_≡_)) (fx₁≡fx₂)
