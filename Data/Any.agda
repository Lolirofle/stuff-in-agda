module Data.Any where

import      Lvl
open import Type

-- A type that can hold a value of any type.
record Any {ℓ} : Type{Lvl.𝐒(ℓ)} where
  constructor intro
  field
    {type} : Type{ℓ}
    value  : type

  map : ∀{T : Type{ℓ}} → (type → T) → Any{ℓ}
  map f = record{value = f(value)}

-- A type that can hold a value of any type in any universe.
record UniversalAny : Typeω where
  constructor intro
  field
    {level} : Lvl.Level
    {type} : Type{level}
    value  : type

  map : ∀{ℓ}{T : Type{ℓ}} → (type → T) → UniversalAny
  map f = record{value = f(value)}
