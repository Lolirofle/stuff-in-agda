module Function where

import      Lvl
open import Type

-- The domain type of a function.
domain : ∀{ℓ₁ ℓ₂} {A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → B) → Type{ℓ₁}
domain{A = A} _ = A

-- The codomain type of a function.
codomain : ∀{ℓ₁ ℓ₂} {A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → B) → Type{ℓ₂}
codomain{B = B} _ = B
