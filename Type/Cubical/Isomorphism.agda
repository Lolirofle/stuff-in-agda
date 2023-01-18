{-# OPTIONS --cubical #-}

module Type.Cubical.Isomorphism where

import      Lvl
open import Type.Cubical.Path.Equality
import      Type.Isomorphism as Type
open import Type

private variable ℓ₁ ℓ₂ : Lvl.Level

-- `Type.Equiv._≍_` specialized to Path.
_≍_ : (A : Type{ℓ₁}) → (B : Type{ℓ₂}) → Type
A ≍ B = A Type.≍ B
{-# BUILTIN EQUIV _≍_ #-}
