import      Lvl
open import Data.Boolean
open import Type

module Data.List.Sorting.Proofs {ℓ} {T : Type{ℓ}} (_≤?_ : T → T → Bool) where

open import Data.Boolean.Proofs
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Proofs
open import Data.List
import      Data.List.Functions as List
open import Data.List.Relation.Membership as Membership using (_∈_ ; use ; skip)
open import Data.List.Relation.Permutation
open import Data.List.Sorting(_≤?_)
open import Data.List.Sorting.Functions(_≤?_)
open import Functional hiding (swap)
open import Lang.Inspect
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator.Properties

-- If a list is sorted, then its tail is also sorted.
tail-sorted-proof : ∀{l} → Sorted(l) → Sorted(List.tail l)
tail-sorted-proof {.∅}           empty                = empty
tail-sorted-proof {_ ⊰ ∅}        single               = empty
tail-sorted-proof {a ⊰ b ⊰ l}    (step ⦃ ab ⦄ ⦃ sl ⦄) = sl

module _ (asym : ∀{x y} → (x ≤? y ≡ not(y ≤? x))) where
  -- Correctness of the sorted property of insert.
  insert-sorted-proof : ∀{x}{l} → Sorted(l) → Sorted(insert x l)
  insert-sorted-proof {x} {∅} sl = single
  insert-sorted-proof {x} {y ⊰ ∅} single with (x ≤? y) | inspect (x ≤?_) y
  ... | 𝑇 | intro p = step ⦃ [↔]-to-[←] IsTrue.is-𝑇 p ⦄
  ... | 𝐹 | intro p rewrite asym{x}{y} = step ⦃ [↔]-to-[←] IsFalse.is-𝐹 p ⦄ ⦃ single ⦄
  insert-sorted-proof {x} {y ⊰ z ⊰ l} (step ⦃ yz ⦄ ⦃ sl ⦄) with (x ≤? y) | inspect (x ≤?_) y
  ... | 𝑇 | intro p = step ⦃ [↔]-to-[←] IsTrue.is-𝑇 p ⦄ ⦃ step ⦃ yz ⦄ ⦃ sl ⦄ ⦄
  ... | 𝐹 | intro p rewrite asym{x}{y} = if-intro {x = x ⊰ z ⊰ l}{y = z ⊰ insert x l}{P = expr ↦ Sorted(y ⊰ expr)}{B = x ≤? z} (xzt ↦ step ⦃ IsFalse.[¬]-elim([↔]-to-[←] IsFalse.is-𝐹 p) ⦄ ⦃ step ⦃ [↔]-to-[←] IsTrue.is-𝑇 xzt ⦄ ⦃ sl ⦄ ⦄) (xzf ↦ step ⦃ yz ⦄ ⦃ if-elimᵣ {x = x ⊰ z ⊰ l}{y = z ⊰ insert x l}{P = Sorted} (insert-sorted-proof {x} {z ⊰ l} sl) xzf ⦄) where
    private variable ℓ₁ : Lvl.Level
    private variable A : Type{ℓ}
    if-elimᵣ : ∀{b : Bool}{x y : A}{P : A → Type{ℓ₁}} → P(if b then x else y) → (b ≡ 𝐹) → P(y)
    if-elimᵣ x [≡]-intro = x

  -- Correctness of the sorted property of merge.
  merge-sorted-proof : ∀{l₁ l₂} → Sorted(l₁) → Sorted(l₂) → Sorted(merge l₁ l₂)
  merge-sorted-proof {l₁} {∅}          s₁ s₂                   = s₁
  merge-sorted-proof {l₁} {x ⊰ ∅}      s₁ single               = insert-sorted-proof s₁
  merge-sorted-proof {l₁} {x ⊰ y ⊰ l₂} s₁ (step ⦃ xy ⦄ ⦃ s₂ ⦄) = insert-sorted-proof (merge-sorted-proof s₁ s₂)

  mergeAll-sorted-proof : ∀{ls} → (∀{l} → ⦃ _ : (l ∈ ls) ⦄ → Sorted(l)) → Sorted(mergeAll ls)
  mergeAll-sorted-proof {∅}      p = empty
  mergeAll-sorted-proof {l ⊰ ls} p = merge-sorted-proof (p ⦃ use (reflexivity(_≡_)) ⦄) (mergeAll-sorted-proof {ls} (\{l} ⦃ q ⦄ → p{l} ⦃ _∈_.skip q ⦄))

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

open import Data using (Unit ; <>)
open import Data.List.Relation.Permutation.Proofs
open import Data.Option
import      Data.Option.Functions as Option
open import Data.Tuple using (_⨯_ ; _,_)
extractMinimal-permutation : ∀{l} → Option.partialMap (∅ permutes l) (\{(x , xs) → (x ⊰ xs) permutes l}) (extractMinimal l)
extractMinimal-permutation {∅} = empty
extractMinimal-permutation {x ⊰ ∅} = prepend empty
extractMinimal-permutation {x ⊰ l@(_ ⊰ _)} with extractMinimal l | extractMinimal-permutation{l}
... | None           | p with () ← permutes-empty-not-empty p
... | (Some(y , l₂)) | p with (x ≤? y)
... | 𝑇 = reflexivity(_permutes_)
... | 𝐹 = trans swap (prepend p)
  
