module Sets.PredicateSet.Listable where

import      Lvl
open import Data.List as List using (List)
open import Data.List.Functions renaming (_++_ to _∪ₗ_) using (singleton)
open import Data.List.Relation.Membership renaming (_∈_ to _∈ₗ_ ; _∈!_ to _∈!ₗ_) using (use ; skip)
open import Data.List.Relation.Permutation
open import Data.List.Relation.Quantification using (∀ₗᵢₛₜ ; module AllElements ; ExistsElement ; ExistsElementEquivalence ; module ExistsElementEquivalence)
open import Functional
open import Lang.Instance
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Sets.PredicateSet using (PredSet ; _∈_ ; ∅ ; _∪_ ; •_)
open        Sets.PredicateSet.BoundedQuantifiers
open import Type.Properties.Singleton
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T : Type{ℓ}
private variable S S₁ S₂ : PredSet{ℓ}(T)
private variable x : T

module _ (S : PredSet{ℓ}(T)) where
  record Listable : Type{Lvl.of(T) Lvl.⊔ ℓ} where
    field
      list : List(T)
      unique : ∀ₛ(S) (_∈!ₗ list)
      restrict : ∀ₗᵢₛₜ(list)  (_∈ S)

    proof : ∀ₛ(S) (_∈ₗ list)
    proof = IsUnit.unit ∘ unique
  list = inst-fn Listable.list

private variable l l₁ l₂ l₁₂ : Listable(S)

∅-listable : Listable{ℓ = ℓ}{T = T}(∅)
Listable.list     ∅-listable = List.∅
Listable.unique   ∅-listable ()
Listable.restrict ∅-listable = AllElements.∅

singleton-listable : Listable(•_ ⦃ [≡]-equiv ⦄ x)
Listable.list     singleton-listable           = singleton _
Listable.unique   singleton-listable [≡]-intro = intro (use [≡]-intro) (\{ {ExistsElement.• x} → ExistsElementEquivalence.use})
Listable.restrict singleton-listable           = [≡]-intro AllElements.⊰ AllElements.∅

{- TODO: Will not satisfy Listable because (_++_) may yield multiples which Listable does not allow, and therefore list-[∪] below is also incorrect.
∪-listable : ⦃ Listable(S₁) ⦄ → ⦃ Listable(S₂) ⦄ → Listable(S₁ ∪ S₂)
Listable.list (∪-listable {S₁ = S₁} {S₂ = S₂}) = list(S₁) ∪ₗ list(S₂)
Listable.unique   ∪-listable = {!!}
Listable.restrict ∪-listable = {!!}-}

-- list-[∪] : ∀{Γ₁ : PredSet{ℓ₁}(Formula(P))}{Γ₂ : PredSet{ℓ₂}(Formula(P))}{l₁₂ : Listable(Γ₁ PredSet.∪ Γ₂)} → Logic.∃{Obj = Listable(Γ₁) ⨯ Listable(Γ₂)}(\(l₁ , l₂) → (list(Γ₁ PredSet.∪ Γ₂) ⦃ l₁₂ ⦄ ≡ (list Γ₁ ⦃ l₁ ⦄) ∪ (list Γ₂ ⦃ l₂ ⦄)))
postulate list-[∪] : (list(S₁ ∪ S₂) ⦃ l₁₂ ⦄ permutes (list S₁ ⦃ l₁ ⦄) ∪ₗ (list S₂ ⦃ l₂ ⦄))
postulate list-[∪·] : (list(S ∪ (•_ ⦃ [≡]-equiv ⦄ x)) ⦃ l₁₂ ⦄ permutes (list S ⦃ l ⦄) ∪ₗ singleton(x))
