open import Data.Boolean
open import Type

module Data.List.Sorting.SelectionSort {ℓ} {T : Type{ℓ}} (_≤?_ : T → T → Bool) where

import      Lvl
open import Data.List
open import Data.List.Functions as List using (_++_)
import      Data.List.Functions.Multi as List
open import Data.List.Sorting.Functions(_≤?_)
open import Data.Option
open import Data.Tuple
import      Numeral.Finite.Conversions as 𝕟
open import Functional using (_∘_)

{-# TERMINATING #-}
selectionSort : List(T) → List(T)
selectionSort l with extractMinimal l
... | Some(x , xs) = x ⊰ selectionSort(xs)
... | None         = l

module Proofs where
