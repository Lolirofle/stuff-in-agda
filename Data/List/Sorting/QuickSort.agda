open import Data.Boolean
open import Type

module Data.List.Sorting.QuickSort {ℓ} {T : Type{ℓ}} (_≤?_ : T → T → Bool) where

import      Lvl
open import Data.List
open import Data.List.Functions as List using (_++_)
import      Data.List.Functions.Multi as List
open import Data.Tuple
import      Numeral.Finite.Conversions as 𝕟
open import Functional using (_∘_)

{-# TERMINATING #-}
quickSort : List(T) → List(T)
quickSort ∅       = ∅
quickSort (x ⊰ l)
  with (less , great) ← List.separateBy(left 𝕟.bool ∘ (x ≤?_)) l
  = quickSort(less) ++ (x ⊰ quickSort(great))

module Proofs where
