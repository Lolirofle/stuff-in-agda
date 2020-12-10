module Data.ListSized where

import      Lvl
open import Numeral.Natural
open import Type

private variable ℓ : Lvl.Level
private variable n : ℕ
private variable T : Type{ℓ}

-- A list is a container/collection with elements in order and which allows multiples
data List (T : Type{ℓ}) : ℕ → Type{ℓ} where
  ∅   : List(T)(𝟎)                     -- An empty list
  _⊰_ : T → List(T)(n) → List(T)(𝐒(n)) -- Cons
infixr 1000 _⊰_

module LongOper where
  pattern empty = ∅
  pattern prepend elem list = elem ⊰ list

-- The list with only a single element
-- singleton : T → List(T)(1)
pattern singleton x = x ⊰ ∅
