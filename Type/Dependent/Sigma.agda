module Type.Dependent.Sigma where

import      Lvl
open import Type

-- Dependent sum type (sigma-type).
-- Also called: Dependent pair type.
-- The right-hand side's type is a function type that uses the left-hand side's type as its "domain".
-- And then the type of the resulting pair depends on the left-hand side.
record Σ {ℓ₁ ℓ₂} (A : Type{ℓ₁}) (B : A → Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  eta-equality
  constructor intro
  field
    left  : A
    right : B(left)
{-# BUILTIN SIGMA Σ #-}
