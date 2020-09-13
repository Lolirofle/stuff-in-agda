import      Lvl
open import Data.Boolean
open import Type

module Data.List.Sorting {ℓ} {T : Type{ℓ}} (_≤?_ : T → T → Bool) where

open import Functional using (_∘₂_)
open import Data.Boolean.Stmt
open import Data.List
open import Data.List.Relation.Permutation
open import Logic

open import Data.List.Relation.OrderedPairwise(IsTrue ∘₂ (_≤?_)) public
  using (empty ; single ; step)
  renaming (OrderedPairwise to Sorted)

-- A sorting algorithm is a function that given a list, always return a sorted list which is a permutation of the original one.
record SortingAlgorithm (f : List(T) → List(T)) : Stmt{Lvl.𝐒(ℓ)} where
  constructor intro
  field
    ⦃ sorts ⦄    : ∀{l} → Sorted(f(l))
    ⦃ permutes ⦄ : ∀{l} → (f(l) permutes l)
