module Structure.Operator.Functions where

import      Lvl
open import Logic
open import Structure.Setoid
open import Structure.Operator.Properties
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ : Lvl.Level

module _ {A : Type{ℓ₁}} {X : Type{ℓ₂}} ⦃ equiv-X : Equiv{ℓₑ₁}(X) ⦄ {Y : Type{ℓ₃}} ⦃ equiv-Y : Equiv{ℓₑ₂}(Y) ⦄ where
  -- `a` is a element which yields the left identity element in the function `f`.
  -- (a ∈ kernelₗ(f)) means (f(a) = id).
  kernelₗ : ∀{_▫_ : X → Y → Y}{id : X} → ⦃ _ : Identityₗ(_▫_)(id) ⦄ → (A → X) → A → Stmt
  kernelₗ {_}{id} (f)(a) = (f(a) ≡ id)

  -- `a` is a element which yields the right identity element in the function `f`.
  -- (a ∈ kernelₗ(f)) means (f(a) = id).
  kernelᵣ : ∀{_▫_ : Y → X → Y}{id : X} → ⦃ _ : Identityᵣ(_▫_)(id) ⦄ → (A → X) → A → Stmt
  kernelᵣ {_}{id} (f)(a) = (f(a) ≡ id)
