module Syntax.Type where

open import Type

-- Assures that a value has a certain type
type-ascript : ∀{ℓ} → (T : Type{ℓ}) → T → T
type-ascript T x = x
{-# INLINE type-ascript #-}

_:-[_] = type-ascript
infixr 0.98 _:-[_]
{-# INLINE _:-[_] #-}

infixl 10 type-ascript
syntax type-ascript T x = x :of: T
