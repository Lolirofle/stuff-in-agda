module Type.Unit {ℓ} where

import      Lvl
open import Relator.Equals
open import Type

-- A type is an unit type when there it has exactly one inhabitant (there is only one object with this type).
-- IsUnit(T) is sometimes also called "T is a singleton", or "T is contractible".
record IsUnit (T : Type{ℓ}) : Type{ℓ} where
  constructor intro
  field
    unit : T
    uniqueness : ∀{x : T} → (x ≡ unit)

-- A type is a mere proposition type when there is at most one inhabitant (there is only one object with this type).
record IsProp (T : Type{ℓ}) : Type{ℓ} where
  constructor intro
  field
    uniqueness : ∀{x y : T} → (x ≡ y)
