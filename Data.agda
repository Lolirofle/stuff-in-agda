module Data where

import      Lvl
open import Type

-- An empty type which cannot be constructed.
-- By default, this should be used to represent _the_ empty type.
data Empty {ℓ} : Type{ℓ} where
{-# FOREIGN GHC data Empty ℓ #-}
{-# COMPILE GHC Empty = data Empty () #-}

-- Empty functions.
-- The empty type eliminator.
-- Any type can be constructed from the empty type.
empty : ∀{ℓ₁ ℓ₂}{T : Type{ℓ₁}} → Empty{ℓ₂} → T
empty ()
{-# COMPILE GHC empty = \_ _ _ e -> case e of{} #-}

-- An unit type which can only be constructed in one way.
-- By default, this should be used to represent _the_ unit type.
record Unit {ℓ} : Type{ℓ} where
  instance constructor <>
open Unit public

{-# BUILTIN UNIT Unit #-}
{-# FOREIGN GHC type Unit ℓ = () #-}
{-# COMPILE GHC Unit = data Unit (()) #-}
