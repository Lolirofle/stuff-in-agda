module Type {lvl} where

open import Level

Type : _
Type = Set(lvl)

-- The empty type which cannot be constructed
data Empty : Type where

-- The unit type which can only be constructed in one way
record Unit : Type where
  constructor unit

-- {-# BUILTIN UNIT Unit #-}
-- {-# COMPILED_DATA Unit () () #-}

-- Assures that a value has a certain type
type-ascription : (T : Type) → T → T
type-ascription T x = x

syntax type-ascription T x = x :of: T

-- Returns the type of a certain value
type-of : {T : Type} → T → Type
type-of {T} _ = T

