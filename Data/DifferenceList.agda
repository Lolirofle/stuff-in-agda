module Data.DifferenceList where

open import Data.List as List using (List)
import      Data.List.Functions as List
import      Lvl
open import Structure.Function
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}

-- Sources:
--   • A Novel Representation of Lists and Its Application to the Function "Reverse" (John Hughes [1986]) [https://www.cs.tufts.edu/~nr/cs257/archive/john-hughes/lists.pdf]
--   • https://github.com/spl/dlist
record DifferenceList (T : Type{ℓ}) ⦃ equiv : Equiv{ℓₑ}(List(T)) ⦄ : Type{ℓ Lvl.⊔ ℓₑ} where
  constructor dlist
  field
    postpendₗᵢₛₜ : List(T) → List(T)
    ⦃ postpendₗᵢₛₜ-function ⦄ : Function(postpendₗᵢₛₜ)
    correctness : ∀{l₁ l₂} → ((postpendₗᵢₛₜ l₁) List.++ l₂ ≡ postpendₗᵢₛₜ(l₁ List.++ l₂)) -- postpendₗᵢₛₜ preserves a right applied List.++
    -- correctness : ∀{l} → ((postpendₗᵢₛₜ List.∅) List.++ l ≡ postpendₗᵢₛₜ(l))
open DifferenceList using (postpendₗᵢₛₜ) public

import      Data.List.Proofs as List
open import Data.List.Equiv
open import Functional
open import Function.Proofs
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity

private variable ℓₑₗ : Lvl.Level

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ equiv-list : Equiv{ℓₑₗ}(List(T)) ⦄ ⦃ ext : Extensionality(equiv-list) ⦄ where
  -- Also called: "rep" in the paper.
  fromList : List(T) → DifferenceList(T)
  fromList l = dlist(l List.++_)
    ⦃ BinaryOperator-unary₂(List._++_) {l} ⦄
    (associativity(List._++_) {l})

  -- Also called: "abs" in the paper.
  list : DifferenceList(T) → List(T)
  list l = postpendₗᵢₛₜ l List.∅

  ∅ : DifferenceList(T)
  ∅ = dlist id
    ⦃ id-function ⦄
    (reflexivity(_≡_))

  singleton : T → DifferenceList(T)
  singleton x = dlist(x List.⊰_)
    ⦃ BinaryOperator-unary₂(List._⊰_) {x} ⦄
    (reflexivity(_≡_))

  prepend : T → DifferenceList(T) → DifferenceList(T)
  prepend x (dlist l p) = dlist((x List.⊰_) ∘ l)
    ⦃ [∘]-function ⦃ func-f = BinaryOperator-unary₂(List._⊰_) {x} ⦄ ⦄
    (congruence₂-₂(List._⊰_)(_) p)

  postpend : T → DifferenceList(T) → DifferenceList(T)
  postpend x (dlist l p) = dlist(l ∘ (x List.⊰_))
    ⦃ [∘]-function ⦃ func-g = BinaryOperator-unary₂(List._⊰_) {x} ⦄ ⦄
    p
  -- \{L} → congruence₂-₁(List._++_)(L) (symmetry(_≡_) (p{x List.⊰ List.∅})) 🝖 {!!}
  -- l ∅ ++ l₁ ≡ l l₁
  -- l(x ⊰ ∅) ++ l₁ ≡ l(x ⊰ l₁)

  -- Also called: "appendR" in the paper.
  _++_ : DifferenceList(T) → DifferenceList(T) → DifferenceList(T)
  (dlist l₁ p₁) ++ (dlist l₂ p₂) = dlist(l₁ ∘ l₂)
    ⦃ [∘]-function {f = l₁}{g = l₂} ⦄
    (p₁ 🝖 congruence₁(l₁) p₂)



  _≡ᵈˡⁱˢᵗ_ : DifferenceList(T) → DifferenceList(T) → Type
  x ≡ᵈˡⁱˢᵗ y = ∀{l} → postpendₗᵢₛₜ x l ≡ postpendₗᵢₛₜ y l



  fromList-list-inverse : ∀{l : DifferenceList(T)} → (fromList(list(l)) ≡ᵈˡⁱˢᵗ l)
  fromList-list-inverse {l = l} = DifferenceList.correctness l

  list-fromList-inverse : ∀{l : List(T)} → list(fromList l) ≡ l
  list-fromList-inverse {l = List.∅}     = reflexivity(_≡_)
  list-fromList-inverse {l = x List.⊰ l} = congruence₂-₂(List._⊰_)(x) (list-fromList-inverse {l = l})

  private variable x : T
  private variable l l₁ l₂ : DifferenceList(T) ⦃ equiv-list ⦄

  list-preserves-∅ : list(∅) ≡ List.∅
  list-preserves-∅ = reflexivity(_≡_)

  list-preserves-singleton : list(singleton(x)) ≡ List.singleton(x)
  list-preserves-singleton = reflexivity(_≡_)

  list-preserves-prepend : list(prepend x l) ≡ List.prepend x (list l)
  list-preserves-prepend = reflexivity(_≡_)

  list-preserves-postpend : list(postpend x l) ≡ List.postpend x (list l)
  list-preserves-postpend{x = x}{l} =
    list(postpend x l)                               🝖[ _≡_ ]-[]
    postpendₗᵢₛₜ l (x List.⊰ List.∅)                 🝖[ _≡_ ]-[]
    postpendₗᵢₛₜ l (List.∅ List.++ List.singleton x) 🝖[ _≡_ ]-[ DifferenceList.correctness l ]-sym
    (postpendₗᵢₛₜ l List.∅) List.++ List.singleton x 🝖[ _≡_ ]-[ List.postpend-[++] ]-sym
    List.postpend x (postpendₗᵢₛₜ l List.∅)          🝖[ _≡_ ]-[]
    List.postpend x (list l)                         🝖-end

  list-preserves-[++] : list(l₁ ++ l₂) ≡ (list l₁) List.++ (list l₂)
  list-preserves-[++] {l₁ = l₁}{l₂ = l₂} =
    postpendₗᵢₛₜ l₁ (postpendₗᵢₛₜ l₂ List.∅)                  🝖[ _≡_ ]-[]
    postpendₗᵢₛₜ l₁ (List.∅ List.++ postpendₗᵢₛₜ l₂ List.∅)   🝖[ _≡_ ]-[ DifferenceList.correctness l₁ ]-sym
    (postpendₗᵢₛₜ l₁ List.∅) List.++ (postpendₗᵢₛₜ l₂ List.∅) 🝖-end
