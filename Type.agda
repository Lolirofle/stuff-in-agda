module Type where

open import Level

Type : _
Type = Set

TypeN : (_ : Level) → _
TypeN n = Set n

data Empty {n} : TypeN n where

record Unit {n} : TypeN n where
  constructor unit

{-# BUILTIN UNIT Unit #-}
-- {-# COMPILED_DATA Unit () () #-}

type-ascription : ∀{lvl} → (T : TypeN lvl) → T → T
type-ascription T x = x

syntax type-ascription T x = x :of: T

