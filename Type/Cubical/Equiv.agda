{-# OPTIONS --cubical #-}

module Type.Cubical.Equiv where

import      Lvl
open import Type.Cubical
open import Type.Cubical.Path.Equality
import      Type.Equiv as Type
open import Type

private variable ℓ₁ ℓ₂ : Lvl.Level

-- `Type.Equiv._≍_` specialized to Path.
_≍_ : (A : Type{ℓ₁}) → (B : Type{ℓ₂}) → Type
A ≍ B = A Type.≍ B
{-# BUILTIN EQUIV _≍_ #-}

instance
  [≍]-reflexivity = \{ℓ} → Type.[≍]-reflexivity {ℓ} ⦃ Path-equiv ⦄

instance
  [≍]-symmetry = \{ℓ} → Type.[≍]-symmetry {ℓ} ⦃ Path-equiv ⦄

instance
  [≍]-transitivity = \{ℓ} → Type.[≍]-transitivity {ℓ} ⦃ Path-equiv ⦄ ⦃ Path-congruence₁ ⦄

instance
  [≍]-equivalence = \{ℓ} → Type.[≍]-equivalence {ℓ} ⦃ Path-equiv ⦄ ⦃ Path-congruence₁ ⦄
