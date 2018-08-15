module Sets.PredicateSet.Filter {ℓₒ} {ℓₒₗ} where

import      Lvl
open import Functional
open import Logic.Propositional
-- open import Sets.PredicateSet
open import Type{ℓₒ Lvl.⊔ ℓₒₗ}

-- An element in Filter(T) is in the subset of T.
-- Something of type Filter(T) is of a restricted part of T.
-- Note: The level of Stmt inside P is lower than Type.
-- TODO: Is this the same as (⊤ ∩ P) in "Sets.PredicateSet"?
record Filter {T : Type} (P : T → Stmt{ℓₒₗ}) : Type where
  constructor subelem
  field
    elem             : T
    ⦃ satisfaction ⦄ : P(elem)

-- postulate nested-subset : ∀{T}{φ₁}{φ₂} → (Tₛ₁ : Filter{T}(φ₁)) → (Tₛ₂ : Filter{Filter{T}(φ₁)}(φ₂)) → Filter{T}(x ↦ φ₁(x) ∧ φ₂(subelem (x) ⦃ ⦄))
-- postulate nested-subset : ∀{T}{φ₁}{φ₂} → (Tₛ₁ : Filter{T}(φ₁)) → (Tₛ₂ : Filter{Filter{T}(φ₁)}(φ₂ ∘ Filter.elem)) → Filter{T}(x ↦ φ₁(x) ∧ φ₂(x))
-- postulate nested-subset : ∀{T}{φ₁}{φ₂} → (Filter{Filter{T}(φ₁)}(φ₂ ∘ Filter.elem) ≡ Filter{T}(x ↦ φ₁(x) ∧ φ₂(x)))

