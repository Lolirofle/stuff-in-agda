open import Data.Boolean
open import Type

module Data.List.Sorting.HeapSort {ℓ} {T : Type{ℓ}} (_≤?_ : T → T → Bool) where

import      Lvl
open import Data.List
import      Data.List.Functions as List
open import Data.BinaryTree
open import Data.BinaryTree.Functions
import      Data.BinaryTree.Heap as Heap
open import Functional using (_∘_)

heapSort : List(T) → List(T)
heapSort = Heap.foldOrdered(_≤?_)(_⊰_) ∅ ∘ List.foldᵣ(Heap.insert(_≤?_)) emptyTree

module Proofs where
  
