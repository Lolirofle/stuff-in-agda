module Relator.Equals.Uniqueness {ℓ₁}{ℓ₂}{ℓ₃} where -- TODO: _≡_ as a parameter

import      Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}
open import Logic.Predicate{ℓ₁ Lvl.⊔ ℓ₃}{ℓ₂}
open import Relator.Equals{ℓ₁ Lvl.⊔ ℓ₃}{ℓ₂}
open import Type

-- Definition of uniqueness of a property.
-- This means that there is at most one element that satisfies this property.
-- This is similiar to "Injective" for functions, but this is for statements.
Uniqueness : ∀{T : Type{ℓ₂}} → (T → Stmt) → Stmt
Uniqueness {T} property = ∀{x y : T} → property(x) → property(y) → (x ≡ y)

-- Definition of existence of an unique element satisfying a property.
-- This means that there is one and only one element that satisfies this property.
∃! : ∀{T} → (T → Stmt) → Stmt
∃! {T} property = ∃(a ↦ property(a)) ∧ Uniqueness{T}(property)

-- TODO: [∃!]-equivalence {T} property = ∃(a ↦ ∃{property(a)}(pa ↦ pa ∧ Uniqueness{T}(property){a}(pa)))

module Theorems where
  -- TODO: Injectivity-Uniqueness : ∀{T} → (∀(z : T) → Uniqueness{T} (a ↦ f(a) ≡ f(z))) ↔ (∀{x y : T} → (f(x) ≡ f(y)) → (x ≡ y))
