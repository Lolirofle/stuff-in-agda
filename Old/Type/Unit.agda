module Type.Unit{ℓ₁}{ℓ₂} where

import      Lvl
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

-- A type is an unit type when there it has exactly one inhabitant (there is only one object with this type).
-- IsUnit(T) is sometimes also called "T is a singleton", or "T is contractible".
record IsUnit (T : Type) : Set(ℓ₁ Lvl.⊔ ℓ₂) where
  constructor intro
  field
    unit : T
    uniqueness : ∀{x : T} → (x ≡ unit)

-- A type is a mere proposition type when there is at most one inhabitant (there is only one object with this type).
record IsProp (T : Type) : Set(ℓ₁ Lvl.⊔ ℓ₂) where
  constructor intro
  field
    uniqueness : ∀{x y : T} → (x ≡ y)
