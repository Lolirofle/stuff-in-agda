{-# OPTIONS --cubical #-}

module Type.Cubical.Path.Properties where

import      Lvl
open import Type
open import Type.Cubical.Path
open import Type.Identity
open import Structure.Relator.Properties
open import Structure.Type.Identity

private variable ℓ : Lvl.Level

-- A type is an identity path type when the path type is equivalent to the identity type.
-- This holds when the type is not a HIT (higher inductive type) (when there are no extra paths in the definition of the type).
IdentityPathType : Type{ℓ} → Type
IdentityPathType(T) = Path{P = T} ⊆₂ Id{T = T}
