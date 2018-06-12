module Relator.Equals.Proofs.Uniqueness {ℓ₁}{ℓ₂}{ℓ₃} where -- TODO: _≡_ as a parameter

import      Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}
open import Logic.Predicate{ℓ₁ Lvl.⊔ ℓ₃}{ℓ₂}
open import Relator.EqualsOld{ℓ₁ Lvl.⊔ ℓ₃}{ℓ₂}
open import Relator.Equals.Uniqueness{ℓ₁}{ℓ₂}{ℓ₃}
open import Type

postulate Injectivity-Uniqueness : ∀{A B}{f : A → B} → (∀(y : B) → Uniqueness{A} (x ↦ y ≡ f(x))) ↔ (∀{x y : A} → (f(x) ≡ f(y)) → (x ≡ y))
