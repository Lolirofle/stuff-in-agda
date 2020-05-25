module Data.List where

import      Lvl
open import Type

private variable ℓ : Lvl.Level

infixr 1000 _⊰_

-- A list is a container/collection of elements.
-- • The elements are in a linear order.
-- • The container allows multiples (non-uniqueness of elements in the container).
data List (T : Type{ℓ}) : Type{ℓ} where
  ∅   : List(T) -- An empty list
  _⊰_ : T → List(T) → List(T) -- Cons
{-# BUILTIN LIST List #-}
