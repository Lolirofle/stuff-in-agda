module Function.Domains where

import      Lvl
open import Structure.Setoid
open import Type

private variable ℓₒ₁ ℓₒ₂ ℓₑ₁ ℓₑ₂ : Lvl.Level

module _ {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} where
  -- The partial domain of a function
  -- Note: This is the same as the domain because all functions are total (or at least supposed to be)
  ⊷ : (X → Y) → Type{ℓₒ₁}
  ⊷ _ = X

module _ {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} where
  -- ∃(Unapply f(y)) is also called "the fiber of the element y under the map f".
  -- Unapply(f) is similar to the inverse image or the preimage of f when their argument is a singleton set.
  Fiber : ⦃ equiv-Y : Equiv{ℓₑ₂}(Y) ⦄ → (X → Y) → Y → X → Type
  Fiber f(y) x = (f(x) ≡ y)
