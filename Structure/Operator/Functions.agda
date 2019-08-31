module Structure.Operator.Functions{ℓ₁}{ℓ₂} where

import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Sets.Setoid{ℓ₁}
open import Structure.Operator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

module _ {A : Type} {X : Type} ⦃ _ : Equiv(X) ⦄ {Y : Type} ⦃ _ : Equiv(Y) ⦄ where
  -- `a` is a element which yields the left identity element in the function `f`.
  -- (a ∈ kernelₗ(f)) means (f(a) = id).
  kernelₗ : ∀{_▫_ : X → Y → Y}{id : X} → ⦃ _ : Identityₗ(_▫_)(id) ⦄ → (A → X) → A → Stmt
  kernelₗ {_}{id} (f)(a) = (f(a) ≡ id)

  -- `a` is a element which yields the right identity element in the function `f`.
  -- (a ∈ kernelₗ(f)) means (f(a) = id).
  kernelᵣ : ∀{_▫_ : Y → X → Y}{id : X} → ⦃ _ : Identityᵣ(_▫_)(id) ⦄ → (A → X) → A → Stmt
  kernelᵣ {_}{id} (f)(a) = (f(a) ≡ id)
