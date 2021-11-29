module Function where

import      Lvl
open import Type

infixl 30 _→ᶠ_ _←_ _←ᶠ_

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A B : Type{ℓ}

-- Function type as a function.
_→ᶠ_ : Type{ℓ₁} → Type{ℓ₂} → Type
A →ᶠ B = A → B

-- Converse of a function type.
_←_ : Type{ℓ₁} → Type{ℓ₂} → Type
B ← A = A → B
_←ᶠ_ = _←_

-- The domain type of a function.
domain : (A → B) → Type
domain{A = A} _ = A

-- The codomain type of a function.
codomain : (A → B) → Type
codomain{B = B} _ = B

-- The identity function.
-- Returns the applied argument.
id : T → T
id(x) = x
{-# INLINE id #-}

-- The constant function.
-- Returns the first argument independent of the second.
const : let _ = A in B → (A → B)
const(x)(_) = x
