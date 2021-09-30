module Type.Properties.Singleton {ℓ ℓₑ} where

import      Lvl
open import Lang.Instance
open import Structure.Setoid
open import Type

-- A type is a singleton type when it has exactly one inhabitant (there is only one object with this type).
-- In other words: There is an unique inhabitant of type T.
-- Also called:
-- • "singleton type"
-- • "unit type"
-- • "contractible"
record IsUnit (T : Type{ℓ}) ⦃ _ : Equiv{ℓₑ}(T) ⦄ : Type{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    unit : T
    uniqueness : ∀{x : T} → (x ≡ unit)
open IsUnit ⦃ ... ⦄ using (unit) public
