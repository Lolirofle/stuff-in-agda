import      Lvl
open import Data.Boolean
open import Type

module Data.List.Sort {ℓ} {T : Type{ℓ}} (_≤?_ : T → T → Bool) where

open import Data.List as List using (List ; ∅ ; _⊰_)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional

module Sorted where
  insert : T → List(T) → List(T)
  insert x ∅       = List.singleton(x)
  insert x (y ⊰ l) = if(x ≤? y) then (x ⊰ y ⊰ l) else (y ⊰ insert x l)

  merge : List(T) → List(T) → List(T)
  merge ∅       b = b
  merge (x ⊰ a) b = merge a (insert x b)

  module _ where
    open import Data
    open import Data.Boolean.Proofs
    open import Data.Boolean.Stmt
    open import Data.Boolean.Stmt.Proofs
    open import Data.List.Relation.OrderedPairwise(IsTrue ∘₂ (_≤?_)) renaming (OrderedPairwise to Sorted)
    open import Lang.Inspect
    open import Logic.Propositional
    open import Relator.Equals
    open import Relator.Equals.Proofs.Equivalence

    tail-sorted-proof : ∀{l} → Sorted(l) → Sorted(List.tail l)
    tail-sorted-proof {.∅}           empty                = Sorted.empty
    tail-sorted-proof {_ ⊰ ∅}        single               = Sorted.empty
    tail-sorted-proof {a ⊰ b ⊰ l}    (step ⦃ ab ⦄ ⦃ sl ⦄) = sl

    module _ (asym : ∀{x y} → (x ≤? y ≡ not(y ≤? x))) (trans : ∀{x y z} → IsTrue(x ≤? y) → IsTrue(y ≤? z) → IsTrue(x ≤? z)) where
      insert-sorted-proof : ∀{x}{l} → Sorted(l) → Sorted(insert x l)
      insert-sorted-proof {x} {∅} sl = single
      insert-sorted-proof {x} {y ⊰ ∅} single with (x ≤? y) | inspect (x ≤?_) y
      ... | 𝑇 | intro p = step ⦃ IsTrue.from-eq p ⦄
      ... | 𝐹 | intro p rewrite asym{x}{y} = step ⦃ IsFalse.from-eq p ⦄ ⦃ single ⦄
      insert-sorted-proof {x} {y ⊰ z ⊰ l} (step ⦃ yz ⦄ ⦃ sl ⦄) with (x ≤? y) | inspect (x ≤?_) y
      ... | 𝑇 | intro p = step ⦃ IsTrue.from-eq p ⦄ ⦃ step ⦃ yz ⦄ ⦃ sl ⦄ ⦄
      ... | 𝐹 | intro p rewrite asym{x}{y} = if-intro {x = x ⊰ z ⊰ l}{y = z ⊰ insert x l}{P = expr ↦ Sorted(y ⊰ expr)}{B = x ≤? z} (xzt ↦ step ⦃ IsFalse.[¬]-elim(IsFalse.from-eq p) ⦄ ⦃ step ⦃ IsTrue.from-eq xzt ⦄ ⦃ sl ⦄ ⦄) (xzf ↦ step ⦃ yz ⦄ ⦃ if-elimᵣ {x = x ⊰ z ⊰ l}{y = z ⊰ insert x l}{P = Sorted} (insert-sorted-proof {x} {z ⊰ l} sl) xzf ⦄)

      merge-sorted-proof : ∀{l₁ l₂} → Sorted(l₁) → Sorted(l₂) → Sorted(merge l₁ l₂)
      merge-sorted-proof {∅} {l₂} a b = b
      merge-sorted-proof {x ⊰ l₁} {l₂} a b = merge-sorted-proof {l₁} {insert x l₂} (tail-sorted-proof a) (insert-sorted-proof b)

split2 : List(T) → (List(T) ⨯ List(T))
split2 ∅           = (∅ , ∅)
split2 (x ⊰ ∅)     = (List.singleton x , ∅)
split2 (x ⊰ y ⊰ l) = Tuple.map (x ⊰_) (y ⊰_) (split2 l)

{-# TERMINATING #-}
merge-sort : List(T) → List(T)
merge-sort = Tuple.uncurry Sorted.merge ∘ Tuple.map1 merge-sort ∘ split2

{-
module Proofs where
  open import Functional
  open import Data
  open import Data.Boolean.Proofs
  open import Data.Boolean.Stmt
  open import Data.Boolean.Stmt.Proofs
  open import Data.List.Relation.OrderedPairwise(IsTrue ∘₂ (_≤?_)) renaming (OrderedPairwise to Sorted)
  open import Lang.Inspect
  open import Logic.Propositional
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equivalence

  module _ (asym : ∀{x y} → (x ≤? y ≡ not(y ≤? x))) (trans : ∀{x y z} → IsTrue(x ≤? y) → IsTrue(y ≤? z) → IsTrue(x ≤? z)) where
    merge-sort-sorted-proof : ∀{l} → Sorted(merge-sort l)
    merge-sort-sorted-proof {∅}         = Sorted.empty
    merge-sort-sorted-proof {a ⊰ ∅}     = single
    merge-sort-sorted-proof l@{_ ⊰ _ ⊰ _} with Tuple.map1 merge-sort (split2 l)
    ... | (a , b) = Sorted.merge-sorted-proof asym trans (merge-sort-sorted-proof{l = ∅}) (merge-sort-sorted-proof{l = l})
-}
