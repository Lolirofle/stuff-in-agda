module Data.Any where

import      Lvl
open import Type

-- A type that can hold a value of any type
record Any {ℓ} : Type{Lvl.𝐒(ℓ)} where
  instance constructor any
  field
    {type} : Type{ℓ}
    value  : type
