module Numeral.Natural.LinearSearch where

open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.List
import      Data.List.Functions as List
open import Data.List.Relation.Membership using (_∈_)
open import Data.List.Relation.Membership.Proofs
open import Data.List.Relation.Quantification
open import Data.List.Relation.Quantification.Proofs
open import Data.List.Sorting
open import Functional
open import Logic.Propositional
open import Numeral.Finite
import      Numeral.Finite.LinearSearch as 𝕟
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Relation.Order
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function

private variable a b n i j : ℕ
private variable f : ℕ → Bool

{-
findBoundedMin : ℕ → ℕ → (ℕ → Bool) → Option(ℕ)
findBoundedMin a b f = Option.map 𝕟-to-ℕ (𝕟.findMin{b −₀ a}(f ∘ (_+ a) ∘ 𝕟-to-ℕ))

findBoundedMin-None-correctness : (a < b) → (findBoundedMin a b f ≡ None) ↔ (∀{i} → (a ≤ i) → (i < b) → IsFalse(f(i)))
findBoundedMin-None-correctness{a}{b}{f} ab
  with [↔]-intro l r ← 𝕟.findMin-None-correctness{b −₀ a}{f ∘ (_+ a) ∘ 𝕟-to-ℕ}
  = [↔]-intro (\p → congruence₁(Option.map 𝕟-to-ℕ) (l (\{i} → p ([≤]-of-[+]ᵣ {𝕟-to-ℕ i}) {![<]-with-[+]-weak ([∨]-introₗ ([∧]-intro ? ?))!}))) (\p{i} ai ib → {!r ? {?}!})
-}

findBoundedAll : ℕ → ℕ → (ℕ → Bool) → List(ℕ)
findBoundedAll a b f = List.map ((_+ a) ∘ 𝕟-to-ℕ) (𝕟.findAll{b −₀ a} (f ∘ (_+ a) ∘ 𝕟-to-ℕ))

findBoundedAll-correctness : AllElements(IsTrue ∘ f)(findBoundedAll a b f)
findBoundedAll-correctness {f} {a} {b} with 𝕟.findAll{b −₀ a} (f ∘ (_+ a) ∘ 𝕟-to-ℕ) | 𝕟.findAll-correctness{b −₀ a}{f ∘ (_+ a) ∘ 𝕟-to-ℕ}
... | ∅     | ∅      = ∅
... | _ ⊰ _ | p ⊰ ps = p ⊰ AllElements-mapᵣ ((_+ a) ∘ 𝕟-to-ℕ) id ps

postulate findBoundedAll-completeness : IsTrue(f(i)) → (a ≤ i) → (i < b) → (i ∈ findBoundedAll a b f)
-- findBoundedAll-completeness {f}{i}{a}{b} ai ib fi = {![∈]-map {f = 𝕟-to-ℕ} (𝕟.findAll-completeness{b −₀ a}{f ∘ (_+ a) ∘ 𝕟-to-ℕ}{ℕ-to-𝕟 (i −₀ a) ⦃ ? ⦄} ?)!}

postulate findBoundedAll-emptyness : (∀{i} → (a ≤ i) → (i < b) → IsFalse(f(i))) ↔ (findBoundedAll a b f ≡ ∅)


postulate findBoundedAll-sorted : Sorted(_≤?_)(findBoundedAll a b f)

postulate findBoundedAll-membership : (i ∈ findBoundedAll a b f) ↔ ((a ≤ i) ∧ (i < b) ∧ IsTrue(f(i)))
