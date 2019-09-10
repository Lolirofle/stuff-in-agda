module Structure.Operator.Functions where

import      Lvl
open import Logic
open import Sets.Setoid
open import Structure.Operator.Properties
open import Type

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type{ℓ₁}} {X : Type{ℓ₂}} ⦃ _ : Equiv(X) ⦄ {Y : Type{ℓ₃}} ⦃ _ : Equiv(Y) ⦄ where
  -- `a` is a element which yields the left identity element in the function `f`.
  -- (a ∈ kernelₗ(f)) means (f(a) = id).
  kernelₗ : ∀{_▫_ : X → Y → Y}{id : X} → ⦃ _ : Identityₗ(_▫_)(id) ⦄ → (A → X) → A → Stmt
  kernelₗ {_}{id} (f)(a) = (f(a) ≡ id)

  -- `a` is a element which yields the right identity element in the function `f`.
  -- (a ∈ kernelₗ(f)) means (f(a) = id).
  kernelᵣ : ∀{_▫_ : Y → X → Y}{id : X} → ⦃ _ : Identityᵣ(_▫_)(id) ⦄ → (A → X) → A → Stmt
  kernelᵣ {_}{id} (f)(a) = (f(a) ≡ id)
