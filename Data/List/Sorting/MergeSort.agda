import      Lvl
open import Data.Boolean
open import Type

module Data.List.Sorting.MergeSort {ℓ} {T : Type{ℓ}} (_≤?_ : T → T → Bool) where

open import Data.List
open import Data.List.Functions as List
open import Data.List.Relation.Membership as Membership using (_∈_ ; use ; skip)
open import Data.List.Relation.Membership.Proofs
open import Data.List.Sorting.Functions(_≤?_)
open import Relator.Equals.Proofs
open import Structure.Relator.Ordering

module _
  (split : List(T) → List(List(T)))
  (_<_ : _)
  ⦃ well-founded : Strict.Properties.WellFounded{ℓ₂ = ℓ}(_<_) ⦄
  ⦃ shrinking-proof : ∀{l}{ll} → ⦃ _ : (ll ∈ split(l)) ⦄ → (ll < l) ⦄
  where

  import Data.List.FunctionsProven as Listₚ

  -- Definition without using well-founded recursion:
  --   merge-sort = Sorted.concat ∘ List.map merge-sort ∘ split
  -- TODO: Correctness requires proof of split(l) being a partition of l
  merge-sort : List(T) → List(T)
  merge-sort = Strict.Properties.wellfounded-recursion(_<_) f where
    f : (l : List(T)) → ((prev : List(T)) → ⦃ _ : prev < l ⦄ → List(T)) → List(T)
    f(l) rec = mergeAll(Listₚ.map (\ll p → rec ll ⦃ shrinking-proof ⦃ p ⦄ ⦄) (split l) [∈]-self)

module Proofs where
  open import Data.Boolean.Stmt
  open import Data.List.Relation.Permutation
  open import Data.List.Sorting(_≤?_)
  open import Data.List.Sorting.Proofs(_≤?_)
  open import Functional using (_∘₂_)
  open import Logic.Propositional
  open import Relator.Equals
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  module _ (asym : ∀{x y} → (x ≤? y ≡ not(y ≤? x))) where -- TODO: Use Structure.Relator.Properties.Asymmetry by the relation (IsTrue ∘₂ (_≤?_))
  -- module _ (asym : ∀{x y} → (x ≤? y ≡ not(y ≤? x))) (trans : ∀{x y z} → IsTrue(x ≤? y) → IsTrue(y ≤? z) → IsTrue(x ≤? z)) where
    {-
    merge-sort-sorted-proof : ∀{l} → Sorted(merge-sort l)
    merge-sort-sorted-proof {∅}         = Sorted.empty
    merge-sort-sorted-proof {a ⊰ ∅}     = single
    merge-sort-sorted-proof l@{_ ⊰ _ ⊰ _} with Tuple.map1 merge-sort (split2 l)
    ... | (a , b) = Sorted.merge-sorted-proof asym trans (merge-sort-sorted-proof{l = ∅}) (merge-sort-sorted-proof{l = l})
    -}
