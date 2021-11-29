module Data.List.Relation where

import      Lvl
import      Data
open import Data.List
open import Logic
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable T : Type{ℓ}

data Empty {ℓ}{T : Type{ℓ}} : List(T) → Stmt{Lvl.𝐒(ℓ)} where
  intro : Empty(∅)
