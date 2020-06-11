module Type.Properties.Inhabited{ℓ} where

import      Lvl
open import Type

-- An inhabited type, which essentially means non-empty (there exists objects with this type), and this object is pointed out/specified/chosen.
-- This means that there exists objects with such an type, and such an object is extractable constructively (like a witness).
-- Also called: Pointed type.
record ◊ (T : Type{ℓ}) : Type{ℓ} where
  constructor intro
  field
    ⦃ existence ⦄ : T
open ◊ ⦃ ... ⦄ renaming (existence to [◊]-existence) public
