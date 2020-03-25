import      Lvl
open import Data.Boolean
open import Type

module Data.List.Sort {ℓ} {T : Type{ℓ}} (_≤?_ : T → T → Bool) where

open import Data.List as List using (List ; ∅ ; _⊰_)
open import Data.List.Relation.Membership as Membership using (_∈_ ; use ; skip)
open import Data.List.Relation.Sublist.Proofs
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Numeral.Natural.Relation.Order
open import Structure.Relator.Ordering

module Sorted where
  -- Inserts an element to a sorted list so that the resulting list is still sorted.
  insert : T → List(T) → List(T)
  insert x ∅       = List.singleton(x)
  insert x (y ⊰ l) = if(x ≤? y) then (x ⊰ y ⊰ l) else (y ⊰ insert x l)

  -- Merges two sorted lists so that the resulting list is still sorted.
  merge : List(T) → List(T) → List(T)
  merge = List.foldᵣ insert
  -- merge ∅       b = b
  -- merge (x ⊰ a) b = merge a (insert x b)

  -- Merges a list of sorted lists so that the resulting list is still sorted.
  concat : List(List(T)) → List(T)
  concat = List.foldᵣ merge ∅

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

    -- If a list is sorted, then its tail is also sorted.
    tail-sorted-proof : ∀{l} → Sorted(l) → Sorted(List.tail l)
    tail-sorted-proof {.∅}           empty                = Sorted.empty
    tail-sorted-proof {_ ⊰ ∅}        single               = Sorted.empty
    tail-sorted-proof {a ⊰ b ⊰ l}    (step ⦃ ab ⦄ ⦃ sl ⦄) = sl

    module _ (asym : ∀{x y} → (x ≤? y ≡ not(y ≤? x))) (trans : ∀{x y z} → IsTrue(x ≤? y) → IsTrue(y ≤? z) → IsTrue(x ≤? z)) where
      -- Correctness of the sorted property of insert.
      insert-sorted-proof : ∀{x}{l} → Sorted(l) → Sorted(insert x l)
      insert-sorted-proof {x} {∅} sl = single
      insert-sorted-proof {x} {y ⊰ ∅} single with (x ≤? y) | inspect (x ≤?_) y
      ... | 𝑇 | intro p = step ⦃ IsTrue.from-eq p ⦄
      ... | 𝐹 | intro p rewrite asym{x}{y} = step ⦃ IsFalse.from-eq p ⦄ ⦃ single ⦄
      insert-sorted-proof {x} {y ⊰ z ⊰ l} (step ⦃ yz ⦄ ⦃ sl ⦄) with (x ≤? y) | inspect (x ≤?_) y
      ... | 𝑇 | intro p = step ⦃ IsTrue.from-eq p ⦄ ⦃ step ⦃ yz ⦄ ⦃ sl ⦄ ⦄
      ... | 𝐹 | intro p rewrite asym{x}{y} = if-intro {x = x ⊰ z ⊰ l}{y = z ⊰ insert x l}{P = expr ↦ Sorted(y ⊰ expr)}{B = x ≤? z} (xzt ↦ step ⦃ IsFalse.[¬]-elim(IsFalse.from-eq p) ⦄ ⦃ step ⦃ IsTrue.from-eq xzt ⦄ ⦃ sl ⦄ ⦄) (xzf ↦ step ⦃ yz ⦄ ⦃ if-elimᵣ {x = x ⊰ z ⊰ l}{y = z ⊰ insert x l}{P = Sorted} (insert-sorted-proof {x} {z ⊰ l} sl) xzf ⦄) where
        private variable ℓ₁ : Lvl.Level
        private variable A : Type{ℓ}
        if-elimᵣ : ∀{b : Bool}{x y : A}{P : A → Type{ℓ₁}} → P(if b then x else y) → (b ≡ 𝐹) → P(y)
        if-elimᵣ x [≡]-intro = x

      -- Correctness of the sorted property of merge.
      merge-sorted-proof : ∀{l₁ l₂} → Sorted(l₁) → Sorted(l₂) → Sorted(merge l₁ l₂)
      merge-sorted-proof {l₁} {∅}          s₁ s₂                   = s₁
      merge-sorted-proof {l₁} {x ⊰ ∅}      s₁ single               = insert-sorted-proof s₁
      merge-sorted-proof {l₁} {x ⊰ y ⊰ l₂} s₁ (step ⦃ xy ⦄ ⦃ s₂ ⦄) = insert-sorted-proof (merge-sorted-proof s₁ s₂)

      concat-sorted-proof : ∀{ls} → (∀{l} → ⦃ _ : (l ∈ ls) ⦄ → Sorted(l)) → Sorted(concat ls)
      concat-sorted-proof {∅}      p = Sorted.empty
      concat-sorted-proof {l ⊰ ls} p = merge-sorted-proof (p ⦃ use ⦄) (concat-sorted-proof {ls} (\{l} ⦃ q ⦄ → p{l} ⦃ _∈_.skip ⦃ q ⦄ ⦄))

      {-
      split₂-sorted-proof : ∀{l} → Sorted(l) → let (a , b) = List.split₂(l) in (Sorted(a) ∧ Sorted(b))
      split₂-sorted-proof {∅}             empty                                 = (Sorted.empty , Sorted.empty)
      split₂-sorted-proof {x ⊰ ∅}         single                                = (single , Sorted.empty)
      split₂-sorted-proof {x ⊰ y ⊰ ∅}     (step ⦃ p ⦄ ⦃ single ⦄)               = (single , single)
      split₂-sorted-proof {x ⊰ y ⊰ z ⊰ l} (step ⦃ xy ⦄ ⦃ step ⦃ yz ⦄ ⦃ szl ⦄ ⦄) = ({!step ⦃ trans xy yz ⦄ ⦃ prevₗ ⦄!} , {!step ⦃ yz ⦄ ⦃ prevᵣ ⦄!}) where
        prev : let (a , b) = List.split₂(z ⊰ l) in (Sorted(a) ∧ Sorted(b))
        prev = split₂-sorted-proof {z ⊰ l} szl

        prevₗ : Sorted(Tuple.left(List.split₂(z ⊰ l)))
        prevₗ = Tuple.left prev

        prevᵣ : Sorted(Tuple.right(List.split₂(z ⊰ l)))
        prevᵣ = Tuple.right prev
      -}

insertion-sort : List(T) → List(T)
insertion-sort = List.foldᵣ Sorted.insert ∅

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
    f(l) rec = Sorted.concat(Listₚ.map (split l) (ll ↦ rec ll))

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
    {-
    merge-sort-sorted-proof : ∀{l} → Sorted(merge-sort l)
    merge-sort-sorted-proof {∅}         = Sorted.empty
    merge-sort-sorted-proof {a ⊰ ∅}     = single
    merge-sort-sorted-proof l@{_ ⊰ _ ⊰ _} with Tuple.map1 merge-sort (split2 l)
    ... | (a , b) = Sorted.merge-sorted-proof asym trans (merge-sort-sorted-proof{l = ∅}) (merge-sort-sorted-proof{l = l})
    -}

    insertion-sort-sorted-proof : ∀{l} → Sorted(insertion-sort l)
    insertion-sort-sorted-proof {∅}     = Sorted.empty
    insertion-sort-sorted-proof {x ⊰ l} = Sorted.insert-sorted-proof asym trans (insertion-sort-sorted-proof {l})
