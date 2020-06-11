module Data.List.Functions.Positional where

import      Lvl
open import Data.List
open import Data.Option
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

-- A singleton list. A list with only a single element.
-- Example:
--   singleton(a) = [a]
singleton : T → List(T)
singleton elem = elem ⊰ ∅

-- The list without its first element (if there is one).
-- Example:
--   tail []      = []
--   tail [a]     = []
--   tail [a,b]   = [b]
--   tail [a,b,c] = [b,c]
tail : List(T) → List(T)
tail ∅ = ∅
tail (_ ⊰ l) = l

-- The first element of the list (head)
first : List(T) → Option(T)
first ∅       = Option.None
first (x ⊰ _) = Option.Some(x)

-- The last element of the list
last : List(T) → Option(T)
last ∅           = Option.None
last (x ⊰ ∅)     = Option.Some(x)
last (_ ⊰ y ⊰ l) = last (y ⊰ l)
-- TODO: Function equivalent to (foldₗ (const Option.Some) Option.None)? Prove if correct
