{-# OPTIONS --prop #-}
module Prop{ℓ} where

open import Agda.Primitive public
  using ()
  renaming (Prop to PROP)
open import Type

Prop : TYPE(_)
Prop = PROP(ℓ)
{-# INLINE Prop #-}

module Prop where
  -- Returns the type of a certain value
  of : ∀{P : Prop} → P → Prop
  of {P} _ = P
  {-# INLINE of #-}
