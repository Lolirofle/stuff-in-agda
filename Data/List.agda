module Data.List where

import      Lvl
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

infixr 1000 _⊰_

-- A list is a container/collection of elements.
-- • The elements are in a linear order.
-- • The container allows multiples (non-uniqueness of elements in the container).
data List (T : Type{ℓ}) : Type{ℓ} where
  ∅   : List(T) -- An empty list
  _⊰_ : T → List(T) → List(T) -- Cons
{-# BUILTIN LIST List #-}

private variable l : List(T)
private variable P : List(T) → Type{ℓ}

elim : P(∅) → (∀(x : T)(l : List(T)) → P(l) → P(x ⊰ l)) → ((l : List(T)) → P(l))
elim base next ∅       = base
elim base next (x ⊰ l) = next(x)(l)(elim base next l)
