module Relator.Equals.Uniqueness {ℓ₁}{ℓ₂} where -- TODO: _≡_ as a parameter

import      Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Type

-- Definition of uniqueness of a property.
-- This means that there is at most one element that satisfies this property.
-- This is similiar to "Injective" for functions, but this is for statements.
Uniqueness : ∀{T} → (T → Stmt) → Stmt
Uniqueness {T} property = ∀{x y : T} → (property(x) ∧ property(y)) → (x ≡ y)

-- Definition of existence of an unique element satisfying a property.
-- This means that there is one and only one element that satisfies this property.
∃! : ∀{T} → (T → Stmt) → Stmt
∃! {T} property = ∃(a ↦ property(a)) ∧ Uniqueness{T}(property)

module Theorems where
  -- TODO: Injectivity-Uniqueness : ∀{T} → (∀(z : T) → Uniqueness{T} (a ↦ f(a) ≡ f(z))) ↔ (∀{x y : T} → (f(x) ≡ f(y)) → (x ≡ y))
