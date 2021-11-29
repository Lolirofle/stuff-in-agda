module Data.List.Combinatorics where

import      Lvl
open import Data
open import Data.List
open import Data.List.Functions
open        Data.List.Functions.LongOper
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Raiseᵣ as Tuple₊ using (_^_)
import      Data.Tuple.Raiseᵣ.Functions as Tuple₊
open import Functional
open import Numeral.Natural
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

-- A list of all non-empty sublists of the specified list.
-- The corresponding counting function is `(2 ^ n) − 1` where `n` is the length of the list.
-- Note:
--   In the inductive case, all of these are permutations of each other:
--   • `foldᵣ (prev ↦ rest ↦ (prev ⊰ (x ⊰ prev) ⊰ rest)) ∅ (sublists₊ l)` (This is used because of its "natural" order)
--   • `foldᵣ (prev ↦ rest ↦ ((x ⊰ prev) ⊰ prev ⊰ rest)) ∅ (sublists₊ l)`
--   • `(map (x ⊰_) (sublists₊ l)) ++ (sublists₊ l)`
--   • `(sublists₊ l) ++ (map (x ⊰_) (sublists₊ l))`
-- Examples:
--   sublists₊ []        = []
--   sublists₊ [1]       = [[1]]
--   sublists₊ [1,2]     = [[1],[2],[1,2]]
--   sublists₊ [1,2,3]   = [[1],[2],[1,2],[3],[1,3],[2,3],[1,2,3]]
--   sublists₊ [1,2,3,4] = [[1],[2],[1,2],[3],[1,3],[2,3],[1,2,3],[4],[1,4],[2,4],[1,2,4],[3,4],[1,3,4],[2,3,4],[1,2,3,4]]
sublists₊ : List(T) → List(List(T))
sublists₊ ∅       = ∅
sublists₊ (x ⊰ l) = singleton(x) ⊰ concatMap(y ↦ (y ⊰ (x ⊰ y) ⊰ ∅)) (sublists₊ l)

-- A list of all sublists of the specified list.
-- This is also the list of all subsets when the given list is a set (distinct elements).
-- The corresponding counting function is `2 ^ n` where `n` is the length of the list.
-- Examples:
--   sublists []        = [[]]
--   sublists [1]       = [[],[1]]
--   sublists [1,2]     = [[],[1],[2],[1,2]]
--   sublists [1,2,3]   = [[],[1],[2],[1,2],[3],[1,3],[2,3],[1,2,3]]
--   sublists [1,2,3,4] = [[],[1],[2],[1,2],[3],[1,3],[2,3],[1,2,3],[4],[1,4],[2,4],[1,2,4],[3,4],[1,3,4],[2,3,4],[1,2,3,4]]
sublists : List(T) → List(List(T))
sublists(l) = ∅ ⊰ sublists₊(l)

-- A list of all combinations of the specified size of the specified list.
-- The corresponding counting function is `𝑐𝐶(n,k)` where `n` is the length of the specified "multiset".
-- All subsets of size `n` from the set `l`.
-- Every unique subset of size n up to set equality.
-- This is also a list of all sublists of the specified size of the specified list.
-- Alternative definition that does not pass the termination checker:
--   combinations : ℕ → List(T) → List(List(T))
--   combinations 0         _ = ∅
--   combinations _         ∅ = ∅
--   combinations 1         l = map singleton l
--   combinations (𝐒(𝐒(n))) l = concat(map f(tails l)) where
--     f : List(T) → List(List(T))
--     f ∅      = ∅
--     f(x ⊰ l) = map (x ⊰_) (combinations (𝐒(n)) l)
-- Examples:
--   combinations _ []          = []
--   combinations 0 [a,b,c,...] = [[]]              when the list is non-empty
--   combinations 1 [a,b,c,...] = [[a],[b],[c],...] when the list is non-empty
--   combinations n l           = []  when (n ≥ length(l))
--   combinations n l           = [l] when (n = length(l))
--   combinations 2 [a,b,c]     = [[a,b],[a,c],[b,c]]
--   combinations 2 [a,b,c,d]   = [[a,b],[a,c],[a,d],[b,c],[b,d],[c,d]]
--   combinations 2 [a,b,c,d,e] = [[a,b],[a,c],[a,d],[a,e],[b,c],[b,d],[b,e],[c,d],[c,e],[d,e]]
--   combinations 3 [a,b,c,d]   = [[a,b,c],[a,b,d],[a,c,d],[b,c,d]]
--   combinations 3 [a,b,c,d,e] = [[a,b,c],[a,b,d],[a,b,e],[a,c,d],[a,c,e],[a,d,e],[b,c,d],[b,c,e],[b,d,e],[c,d,e]]
--   combinations 4 [a,b,c,d,e] = [[a,b,c,d],[a,b,c,e],[a,b,d,e],[a,c,d,e],[b,c,d,e]]
combinations : (k : ℕ) → List(T) → List(T ^ k)
combinations 0         _         = singleton(<>)
combinations (𝐒(_))    ∅         = ∅
combinations 1         l@(_ ⊰ _) = l
combinations (𝐒(𝐒(k))) (x ⊰ l)   = (map(x ,_) (combinations (𝐒(k)) l)) ++ (combinations(𝐒(𝐒(k))) l)

-- The corresponding counting function is `𝑐𝐶(n + k − 1 , k)` where `n` is the length of the specified "multiset".
-- Examples:
--   repeatableCombinations _ []          = []
--   repeatableCombinations 0 [a,b,c,...] = [[]]              when the list is non-empty
--   repeatableCombinations 1 [a,b,c,...] = [[a],[b],[c],...] when the list is non-empty
--   repeatableCombinations n [a]         = [repeat n a]
--   repeatableCombinations 2 [a,b]       = [[a,a],[a,b],[b,b]]
--   repeatableCombinations 2 [a,b,c]     = [[a,a],[a,b],[a,c],[b,b],[b,c],[c,c]]
--   repeatableCombinations 3 [a,b]       = [[a,a,a],[a,a,b],[a,b,b],[b,b,b]]
--   repeatableCombinations 3 [a,b,c]     = [[a,a,a],[a,a,b],[a,a,c],[a,b,b],[a,b,c],[a,c,c],[b,b,b],[b,b,c],[b,c,c],[c,c,c]]
--   repeatableCombinations 4 [a,b]       = [[a,a,a,a],[a,a,a,b],[a,a,b,b],[a,b,b,b],[b,b,b,b]]
--   repeatableCombinations 4 [a,b,c]     = [[a,a,a,a],[a,a,a,b],[a,a,a,c],[a,a,b,b],[a,a,b,c],[a,a,c,c],[a,b,b,b],[a,b,b,c],[a,b,c,c],[a,c,c,c],[b,b,b,b],[b,b,b,c],[b,b,c,c],[b,c,c,c],[c,c,c,c]]
repeatableCombinations : (k : ℕ) → List(T) → List(T ^ k)
repeatableCombinations 0         _         = singleton(<>)
repeatableCombinations (𝐒(_))    ∅         = ∅
repeatableCombinations 1         l@(_ ⊰ _) = l
repeatableCombinations (𝐒(𝐒(k))) (x ⊰ l)   = (map (x ,_) (repeatableCombinations (𝐒(k)) (x ⊰ l))) ++ (repeatableCombinations (𝐒(𝐒(k))) l)

-- A list of all tuples of length `n` from the "multiset" `l`.
-- Every tuple combination of length `n`.
-- The corresponding counting function is `k ^ n` where `k` is the length of the list.
-- Examples:
--   tuples 0 [a]     = [()]
--   tuples 1 [a]     = [a]
--   tuples 2 [a]     = [(a,a)]
--   tuples 0 [a,b]   = [()]
--   tuples 1 [a,b]   = [a,b]
--   tuples 2 [a,b]   = [(a,a) , (a,b) , (b,a) , (b,b)]
--   tuples 0 [a,b,c] = [()]
--   tuples 1 [a,b,c] = [a,b,c]
--   tuples 2 [a,b,c] = [(a,a) , (a,b) , (a,c) , (b,a) , (b,b) , (b,c) , (c,a) , (c,b), (c,c)]
tuples : (n : ℕ) → List(T) → List(T ^ n)
tuples 0           = const(singleton(<>))
tuples 1           = id
tuples (𝐒(𝐒(n))) l = concatMap(x ↦ map (Tuple₊.prepend x) (tuples (𝐒(n)) l)) l

-- A list of all rotations of a list.
-- Examples:
--   rotations []        = []
--   rotations [a]       = [[a]]
--   rotations [a,b]     = [[a,b] , [b,a]]
--   rotations [a,b,c]   = [[a,b,c] , [b,c,a] , [c,a,b]]
--   rotations [a,b,c,d] = [[a,b,c,d] , [b,c,d,a] , [c,d,a,b] , [d,a,b,c]]
rotations : List(T) → List(List(T))
rotations l = accumulateIterate₀(length l) rotateₗ l

-- Accumulated `insertAt` for every position of the given list.
-- Examples:
--   insertedEverywhere i []        = [[i]]
--   insertedEverywhere i [a]       = [[i,a],[a,i]]
--   insertedEverywhere i [a,b]     = [[i,a,b],[a,i,b],[a,b,i]]
--   insertedEverywhere i [a,b,c]   = [[i,a,b,c],[a,i,b,c],[a,b,i,c],[a,b,c,i]]
--   insertedEverywhere i [a,b,c,d] = [[i,a,b,c,d],[a,i,b,c,d],[a,b,i,c,d],[a,b,c,i,d],[a,b,c,d,i]
insertedEverywhere : T → List(T) → List(List(T))
insertedEverywhere i ∅       = singleton(singleton i)
insertedEverywhere i (x ⊰ l) = (i ⊰ x ⊰ l) ⊰ (map (prepend x) (insertedEverywhere i l))

-- Every reordering of the list's elements.
-- Examples:
--   permutations []        = [[]]
--   permutations [a]       = [[a]]
--   permutations [a,b]     = [[a,b],[b,a]]
--   permutations [a,b,c]   = [[a,b,c],[b,a,c],[b,c,a],[a,c,b],[c,a,b],[c,b,a]]
--   permutations [a,b,c,d] = [[a,b,c,d],[b,a,c,d],[b,c,a,d],[b,c,d,a],[a,c,b,d],[c,a,b,d],[c,b,a,d],[c,b,d,a],[a,c,d,b],[c,a,d,b],[c,d,a,b],[c,d,b,a],[a,b,d,c],[b,a,d,c],[b,d,a,c],[b,d,c,a],[a,d,b,c],[d,a,b,c],[d,b,a,c],[d,b,c,a],[a,d,c,b],[d,a,c,b],[d,c,a,b],[d,c,b,a]]
permutations : List(T) → List(List(T))
permutations ∅               = singleton(∅)
permutations (x ⊰ ∅)         = singleton(singleton x)
permutations (x ⊰ l@(_ ⊰ _)) = concatMap (insertedEverywhere x) (permutations l)
