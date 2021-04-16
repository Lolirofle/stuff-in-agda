import      Lvl
open import Data.Boolean
open import Type

module Data.List.Sorting.Functions {ℓ} {T : Type{ℓ}} (_≤?_ : T → T → Bool) where

open import Data.List
import      Data.List.Functions as List

-- Inserts an element to a sorted list so that the resulting list is still sorted.
insert : T → List(T) → List(T)
insert x ∅       = List.singleton(x)
insert x (y ⊰ l) = if(x ≤? y) then (x ⊰ y ⊰ l) else (y ⊰ insert x l)

-- Merges two sorted lists so that the resulting list is still sorted.
merge : List(T) → List(T) → List(T)
merge = List.foldᵣ insert

-- Merges a list of sorted lists so that the resulting list is still sorted.
mergeAll : List(List(T)) → List(T)
mergeAll = List.foldᵣ merge ∅

open import Data.Tuple
open import Data.Option
import      Data.Option.Functions as Option

-- Extracts a smallest element from a list.
extractMinimal : List(T) → Option(T ⨯ List(T))
extractMinimal ∅               = None
extractMinimal (x ⊰ ∅)         = Some(x , ∅)
extractMinimal (x ⊰ l@(_ ⊰ _)) = Option.map(\{(la , las) → if(x ≤? la) then (x , l) else (la , x ⊰ las)}) (extractMinimal l)
