module Sets.Subset {ℓₒ} {ℓₒₗ} where -- {ℓₗ}

import      Lvl
open import Functional
open import Logic.Propositional
open import Type{ℓₒ Lvl.⊔ ℓₒₗ}

-- An element in Subset(T) is in the subset of T.
-- Something of type Subset(T) is of a restricted part of T.
-- Note: The level of Stmt inside P is lower than Type.
record Subset {T : Type} (P : T → Stmt{ℓₒₗ}) : Type where -- TODO: Cannot be Type?
  constructor subelem
  field
    elem             : T
    ⦃ satisfaction ⦄ : P(elem)

-- postulate nested-subset : ∀{T}{φ₁}{φ₂} → (Tₛ₁ : Subset{T}(φ₁)) → (Tₛ₂ : Subset{Subset{T}(φ₁)}(φ₂)) → Subset{T}(x ↦ φ₁(x) ∧ φ₂(subelem (x) ⦃ ⦄))
postulate nested-subset : ∀{T}{φ₁}{φ₂} → (Tₛ₁ : Subset{T}(φ₁)) → (Tₛ₂ : Subset{Subset{T}(φ₁)}(φ₂ ∘ Subset.elem)) → Subset{T}(x ↦ φ₁(x) ∧ φ₂(x))
-- nested-subset

{-open import Logic.Predicate

record SubElem2 (T : Type) : Type where
  constructor subelem
  field
    elem  : T
    .func : ∃(A ↦ A → T)
-}
