module DependentFunction where

import      Lvl
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable A : Type{ℓ}
private variable B : A → Type{ℓ}

-- Function type as a function.
_→ᶠ_ : (A : Type{ℓ₁}) → (A → Type{ℓ₂}) → Type{ℓ₁ Lvl.⊔ ℓ₂}
A →ᶠ B = (a : A) → B(a)
infixl 30 _→ᶠ_

-- The domain type of a function.
domain : (A →ᶠ B) → Type
domain{A = A} _ = A

-- The codomain type of a function.
codomain : (A →ᶠ B) → (A → Type)
codomain{B = B} _ = B
