module Type.Properties.Empty{ℓₜ ℓ} where

import      Lvl
open import Type

-- A type is empty when an "empty function" exist for it.
-- An empty type is an uninhabited type: It is not possible to construct objects of this type.
-- This definition works because the consistent type system in Agda ensures that empty function only exist for empty types.
-- The reason for having this is because the empty type is not unique (There are an infinite number of "empty types" because types are not equal to each other extensionally (unlike sets, type equality is not based on their inhabitants (set equality is based on which elements that the set contains). Type equality is nominal.)).
-- Example of non-uniqueness:
--   `data Empty : Type where` defines an empty type.
--   `data Empty2 : Type where` also defines an empty type.
--   Now, `Empty` is not type equal to `Empty2` because the terms does not normalize further (by the rules of the language).
record IsEmpty (E : Type{ℓ}) : Type{Lvl.𝐒(ℓₜ) Lvl.⊔ ℓ} where
  constructor intro
  field
    -- Empty functions for an empty type
    -- For any type T, it is always possible to construct a function from an empty type E to T.
    -- Note: This is an eliminator for an empty type.
    empty : ∀{T : Type{ℓₜ}} → E → T
open IsEmpty ⦃ … ⦄ public
