module Data where

import      Lvl
open import Type

-- The empty type which cannot be constructed
data Empty {ℓ} : Type{ℓ} where

-- Empty function
empty : ∀{ℓ₁ ℓ₂}{T : Type{ℓ₁}} → Empty{ℓ₂} → T
empty ()

-- The unit type which can only be constructed in one way
record Unit {ℓ} : Type{ℓ} where
  instance constructor <>
open Unit public

{-# BUILTIN UNIT Unit #-}
{-# FOREIGN GHC type AgdaUnit ℓ = () #-}
{-# COMPILE GHC Unit = data AgdaUnit (()) #-}
