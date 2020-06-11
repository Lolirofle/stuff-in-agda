module Data.Option where

import      Lvl
open import Data
open import Type

private variable ℓ : Lvl.Level

data Option (T : Type{ℓ}) : Type{ℓ} where
  None : Option(T)
  Some : T → Option(T)
