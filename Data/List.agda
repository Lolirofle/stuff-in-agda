module Data.List where

import      Lvl
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

-- A list is a container/collection of elements.
-- • The elements are in a linear order.
-- • The container allows multiples (non-uniqueness of elements in the container).
data List (T : Type{ℓ}) : Type{ℓ} where
  ∅   : List(T)               -- Empty list
  _⊰_ : T → List(T) → List(T) -- Cons/prepend
{-# BUILTIN LIST List #-}
open List using () renaming (∅ to empty ; _⊰_ to prepend) public
pattern _⊱_ l x = _⊰_ x l
infixr 1000 _⊰_
infixl 1000 _⊱_

module _
  (P : List(T) → Type{ℓ})
  (base : P(∅))
  (step : ∀(x : T)(l : List(T)) → P(l) → P(x ⊰ l))
  where

  elim : ((l : List(T)) → P(l))
  elim ∅       = base
  elim (x ⊰ l) = step x l (elim l)
