module Structure.Operator.Monoid.Homomorphism where

import      Lvl
open import Logic
open import Logic.Predicate
open import Structure.Function
open import Structure.Function.Multi
open import Structure.Operator.Monoid
open import Structure.Setoid
open import Type

record Homomorphism
  {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂}
  {X : Type{ℓ₁}} ⦃ _ : Equiv{ℓₑ₁}(X) ⦄ {_▫X_ : X → X → X} ( structureₗ : Monoid(_▫X_))
  {Y : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(Y) ⦄ {_▫Y_ : Y → Y → Y} ( structureᵣ : Monoid(_▫Y_))
  (f : X → Y)
  : Stmt{ℓ₁ Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓₑ₂} where

  constructor intro

  idₗ = Monoid.id(structureₗ)
  idᵣ = Monoid.id(structureᵣ)

  field
    ⦃ function ⦄ : Function(f)
    ⦃ preserve-op ⦄ : Preserving₂(f)(_▫X_)(_▫Y_)
    ⦃ preserve-id ⦄ : Preserving₀(f)(idₗ)(idᵣ)

_→ᵐᵒⁿᵒⁱᵈ_ : ∀{ℓₗ ℓₗₑ ℓᵣ ℓᵣₑ} → MonoidObject{ℓₗ}{ℓₗₑ} → MonoidObject{ℓᵣ}{ℓᵣₑ} → Type
A →ᵐᵒⁿᵒⁱᵈ B = ∃(Homomorphism(MonoidObject.monoid A)(MonoidObject.monoid B))
