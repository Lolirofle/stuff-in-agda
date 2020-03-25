module Data.List.Combinatorics where

import      Lvl
open import Data
open import Data.List
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Raise as Tuple₊ using (_^_)
open import Functional
open import Numeral.Natural
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

-- A list of all non-empty sublists of the specified list.
sublists₊ : List(T) → List(List(T))
sublists₊ ∅       = ∅
sublists₊ (x ⊰ l) = singleton(x) ⊰ foldᵣ (prev ↦ rest ↦ (prev ⊰ (x ⊰ prev) ⊰ rest)) ∅ (sublists₊ l)

-- A list of all sublists of the specified list.
sublists : List(T) → List(List(T))
sublists(l) = ∅ ⊰ sublists₊(l)

-- A list of all tuples of length n from the "multiset" l.
-- Every tuple combination of length n.
-- Example:
--   tuples 2 [a,b,c] = [(a,a) , (a,b) , (a,c) , (b,a) , (b,b) , (b,c) , (c,a) , (c,b), (c,c)]
tuples : (n : ℕ) → List(T) → List(T ^ n)
tuples 0           = const(singleton(<>))
tuples 1           = id
tuples (𝐒(𝐒(n))) l = concat(map (x ↦ map (x Tuple₊.⊰_) (tuples (𝐒(n)) l)) l)

{-
-- All subsets of size n from the set l.
-- Every unique subset of size n up to set equality.
combinations : ℕ → List(T) → List(List(T))
combinations 0         _  = ∅
combinations _         ∅ = ∅
combinations 1         l  = map singleton l
combinations (𝐒(𝐒(n))) l  = concat(map f(tails l)) where
  f : List(T) → List(List(T))
  f ∅      = ∅
  f(x ⊰ l) = map (x ⊰_) (combinations (𝐒(n)) l)
-}
