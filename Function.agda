module Function where

import      Lvl
open import Type

infixl 30 _→ᶠ_ _←_ _←ᶠ_

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable A B : Type{ℓ}

-- Function type as a function.
_→ᶠ_ : Type{ℓ₁} → Type{ℓ₂} → Type
X →ᶠ Y = X → Y

-- Converse of a function type.
_←_ : Type{ℓ₁} → Type{ℓ₂} → Type
Y ← X = X → Y
_←ᶠ_ = _←_

-- The domain type of a function.
domain : (A → B) → Type
domain{A = A} _ = A

-- The codomain type of a function.
codomain : (A → B) → Type
codomain{B = B} _ = B
