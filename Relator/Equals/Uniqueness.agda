module Relator.Equals.Uniqueness {ℓ₁}{ℓ₂}{ℓ₃} where -- TODO: Move to Relator.Equivalence.Uniqueness. Is ℓ₃ really neccessary?

import      Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}
open import Logic.Predicate{ℓ₁ Lvl.⊔ ℓ₃}{ℓ₂}
open import Sets.Setoid{ℓ₁ Lvl.⊔ ℓ₃}
open import Type

-- Definition of uniqueness of a property.
-- This means that there is at most one element that satisfies this property.
-- This is similiar to "Injective" for functions, but this is for statements.
Unique : ∀{T : Type{ℓ₂}} → ⦃ _ : Equiv(T) ⦄ → (T → Stmt) → Stmt
Unique {T} property = ∀{x y : T} → property(x) → property(y) → (x ≡ y)

-- Definition of existence of an unique element satisfying a property.
-- This means that there is one and only one element that satisfies this property.
∃! : ∀{T} → ⦃ _ : Equiv(T) ⦄ → (T → Stmt) → Stmt
∃! {T} property = ∃(a ↦ property(a)) ∧ Unique{T}(property)

[∃!]-intro : ∀{T} → ⦃ _ : Equiv(T) ⦄ → ∀{property} → ∃(property) → Unique{T}(property) → ∃!(property)
[∃!]-intro = [∧]-intro

[∃!]-existence  = [∧]-elimₗ
[∃!]-uniqueness = [∧]-elimᵣ

-- TODO: [∃!]-equivalence {T} property = ∃(a ↦ ∃{property(a)}(pa ↦ pa ∧ Uniqueness{T}(property){a}(pa)))
