module Type.Empty where

import Lvl

-- A type is empty when "empty functions" exists for it.
-- This is an useful definition because there are an infinite number of "empty types".
-- An explanation for why there are an infinite number of them:
-- · Types are not equal to each other extentionally (unlike sets, type equality is not based on their inhabitants (set equality is based on which elements that the set contains)).
-- An alternative explanation:
-- · Type equality is nominal (loosely: based on its name (assuming no other type could be named the same)), and not representional.
-- Or more simply:
-- · `data Empty : Type where` defines an empty type.
--   `data Empty2 : Type where` also defines an empty type.
--   Now, `Empty` is not type equal to `Empty2` because the terms does not normalize further (by the rules of the language).
-- So by proving IsEmpty(T), it means that the type T is empty, because empty types are the only types that has the property of having empty functions.
record IsEmpty {ℓ₁ ℓ₂} (T : Set(ℓ₁)) : Set(Lvl.𝐒(ℓ₁ Lvl.⊔ ℓ₂)) where
  constructor intro
  field
    -- Empty functions for the empty type
    empty : ∀{U : Set(ℓ₂)} → T → U
open IsEmpty ⦃ ... ⦄
