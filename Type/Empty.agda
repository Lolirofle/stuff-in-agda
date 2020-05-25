module Type.Empty{ℓ} where

import      Lvl
open import Type

-- A type is empty when "empty functions" exists for it, which essentially means that there are no objects with this type.
-- This is an useful definition because the empty type is not unique (Actually there are an infinite number of "empty types").
-- An explanation for why there are an infinite number of them:
-- · Types are not equal to each other extensionally (unlike sets, type equality is not based on their inhabitants (set equality is based on which elements that the set contains)).
-- An alternative explanation:
-- · Type equality is nominal (loosely: based on its name (assuming no other type could be named the same)), and not representional.
-- Or more simply by an example:
-- · `data Empty : Type where` defines an empty type.
--   `data Empty2 : Type where` also defines an empty type.
--   Now, `Empty` is not type equal to `Empty2` because the terms does not normalize further (by the rules of the language).
-- So by proving IsEmpty(T), it means that the type T is empty, because empty types are the only types that has the property of having empty functions.
record IsEmpty (T : Type{ℓ}) : Type{Lvl.𝐒(ℓ)} where
  constructor intro
  field
    -- Empty functions for an empty type
    -- For any type U, it is always possible to construct a function from T to U if T is empty
    empty : ∀{U : Type{ℓ}} → T → U

-- An inhabited type, which essentially means non-empty (there exists objects with this type).
-- This means that there exists objects with such an type.
record ◊ (T : Type{ℓ}) : Type{ℓ} where
  constructor intro
  field
    ⦃ existence ⦄ : T
open ◊ ⦃ ... ⦄ renaming (existence to [◊]-existence) public
