module Data where

import      Lvl
open import Type

-- An empty type which cannot be constructed.
-- By default, this should be used to represent _the_ empty type.
data Empty {ℓ} : Type{ℓ} where

-- Empty functions.
-- The empty type eliminator.
-- Any type can be constructed from the empty type.
empty : ∀{ℓ₁ ℓ₂}{T : Type{ℓ₁}} → Empty{ℓ₂} → T
empty ()

-- An unit type which can only be constructed in one way.
-- By default, this should be used to represent _the_ unit type.
record Unit {ℓ} : Type{ℓ} where
  instance constructor <>
open Unit public

{-# BUILTIN UNIT Unit #-}
{-# FOREIGN GHC type AgdaUnit ℓ = () #-}
{-# COMPILE GHC Unit = data AgdaUnit (()) #-}
