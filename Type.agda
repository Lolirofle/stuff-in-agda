module Type {lvl} where

open import Level

Type : _
Type = Set(lvl)

data Empty : Type where

record Unit : Type where
  constructor unit

-- {-# BUILTIN UNIT Unit #-}
-- {-# COMPILED_DATA Unit () () #-}

type-ascription : (T : Type) → T → T
type-ascription T x = x

syntax type-ascription T x = x :of: T

type-of : {T : Type} → T → Type
type-of {T} _ = T

