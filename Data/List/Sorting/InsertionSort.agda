import      Lvl
open import Data.Boolean
open import Type

module Data.List.Sorting.InsertionSort {ℓ} {T : Type{ℓ}} (_≤?_ : T → T → Bool) where

open import Data.List
import      Data.List.Functions as List
open import Data.List.Sorting.Functions(_≤?_)

insertion-sort : List(T) → List(T)
insertion-sort = List.foldᵣ insert ∅

module Proofs where
  open import Data.Boolean.Stmt
  open import Data.List.Relation.Permutation
  open import Data.List.Relation.Permutation.Proofs
  open import Data.List.Sorting(_≤?_)
  open import Data.List.Sorting.Proofs(_≤?_)
  open import Functional using (_∘₂_)
  open import Logic.Propositional
  open import Relator.Equals
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  module _ (asym : ∀{x y} → (x ≤? y ≡ not(y ≤? x))) where -- TODO: Use Structure.Relator.Properties.Asymmetry by the relation (IsTrue ∘₂ (_≤?_))
    instance
      insertion-sort-sorted-proof : ∀{l} → Sorted(insertion-sort l)
      insertion-sort-sorted-proof {∅}     = empty
      insertion-sort-sorted-proof {x ⊰ l} = insert-sorted-proof asym (insertion-sort-sorted-proof {l})

    insert-permutation-proof : ∀{x}{l} → ((insert x l) permutes (x ⊰ l))
    insert-permutation-proof {x} {∅} = prepend _permutes_.empty
    insert-permutation-proof {x} {a ⊰ l} with (x ≤? a)
    ... | 𝑇 = reflexivity(_permutes_)
    ... | 𝐹 =
      a ⊰ insert x l 🝖-[ _permutes_.prepend (insert-permutation-proof {x} {l}) ]
      a ⊰ x ⊰ l      🝖-[ _permutes_.swap ]
      x ⊰ a ⊰ l      🝖-end

    instance
      insertion-sort-permutation-proof : ∀{l} → ((insertion-sort l) permutes l)
      insertion-sort-permutation-proof {∅} = _permutes_.empty
      insertion-sort-permutation-proof {x ⊰ l} =
        insertion-sort (x ⊰ l) 🝖-[ insert-permutation-proof ]
        x ⊰ (insertion-sort l) 🝖-[ prepend (insertion-sort-permutation-proof {l}) ]
        x ⊰ l                  🝖-end

    instance
      insertion-sort-sorting-algorithm : SortingAlgorithm(insertion-sort)
      SortingAlgorithm.sorts    insertion-sort-sorting-algorithm {l} = insertion-sort-sorted-proof {l}
      SortingAlgorithm.permutes insertion-sort-sorting-algorithm     = insertion-sort-permutation-proof
