module Relator.Equals.Proofs.Uniqueness {ℓ₁}{ℓ₂}{ℓ₃} where -- TODO: _≡_ as a parameter

import      Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}
open import Logic.Predicate{ℓ₁ Lvl.⊔ ℓ₃}{ℓ₂}
open import Relator.EqualsOld{ℓ₁ Lvl.⊔ ℓ₃}{ℓ₂}
open import Relator.Equals.Uniqueness{ℓ₁}{ℓ₂}{ℓ₃}
open import Relator.Equals.Proofs{ℓ₁ Lvl.⊔ ℓ₃}{ℓ₂}
open import Structure.Function.Domain{ℓ₁ Lvl.⊔ ℓ₃}
open import Structure.Relator.Properties{ℓ₁ Lvl.⊔ ℓ₃}{ℓ₂}
open import Type

Uniqueness-Injectivity : ∀{A : Type{ℓ₂}}{B : Type{ℓ₂}}{f : A → B} → (∀{y : B} → Unique{A} (x ↦ y ≡ f(x))) ↔ Injective(f)
Uniqueness-Injectivity {A}{B} {f} = [↔]-intro l r where
  l : (∀{y : B} → Unique{A} (x ↦ y ≡ f(x))) ← Injective(f)
  l (injective) {y} {x₁}{x₂} (y≡fx₁) (y≡fx₂) = injective {x₁}{x₂} (symmetry(y≡fx₁) 🝖 (y≡fx₂))

  r : (∀{y : B} → Unique{A} (x ↦ y ≡ f(x))) → Injective(f)
  r (unique) {x₁}{x₂} (fx₁≡fx₂) = unique {f(x₁)}{x₁}{x₂} ([≡]-intro) (fx₁≡fx₂)

