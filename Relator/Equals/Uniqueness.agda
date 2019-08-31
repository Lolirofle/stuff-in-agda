module Relator.Equals.Uniqueness where -- TODO: Move to Relator.Equivalence.Uniqueness. Is ℓ₃ really neccessary?

import      Lvl
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid
open import Type

module _ {ℓ₁}{ℓ₂} where
  -- Definition of uniqueness of a property.
  -- This means that there is at most one element that satisfies this property.
  -- This is similiar to "Injective" for functions, but this is for statements.
  Unique : ∀{T : Type{ℓ₁}} → ⦃ _ : Equiv(T) ⦄ → (T → Stmt{ℓ₂}) → Stmt
  Unique {T} property = ∀{x y : T} → property(x) → property(y) → (x ≡ y)

  -- Definition of existence of an unique element satisfying a property.
  -- This means that there is one and only one element that satisfies this property.
  ∃! : ∀{T : Type{ℓ₁}} → ⦃ _ : Equiv(T) ⦄ → (T → Stmt{ℓ₂}) → Stmt
  ∃! {T} property = ∃(a ↦ property(a)) ∧ Unique{T}(property)

  [∃!]-intro : ∀{T} → ⦃ _ : Equiv(T) ⦄ → ∀{property} → ∃(property) → Unique{T}(property) → ∃!(property)
  [∃!]-intro = [∧]-intro

  [∃!]-existence  = [∧]-elimₗ
  [∃!]-uniqueness = [∧]-elimᵣ

  -- TODO: [∃!]-equivalence {T} property = ∃(a ↦ ∃{property(a)}(pa ↦ pa ∧ Uniqueness{T}(property){a}(pa)))
