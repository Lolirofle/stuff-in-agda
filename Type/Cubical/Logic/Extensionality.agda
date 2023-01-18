{-# OPTIONS --cubical #-}

module Type.Cubical.Logic.Extensionality where

open import BidirectionalFunction using (_↔_ ; _$ₗ_ ; _$ᵣ_ ; intro)
open import BidirectionalFunction.Equiv
open import Function
open import Logic.Predicate
import      Lvl
open import Structure.Function.Domain using (intro ; Inverseₗ ; Inverseᵣ)
open import Structure.Relator.Properties
open import Type.Cubical.Path
open import Type.Cubical.Path.Equality using (Path-sub-of-reflexive)
open import Type.Cubical.Path.Univalence using (type-extensionality)
open import Type.Properties.MereProposition
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A B P Q : Type{ℓ}

module _ ⦃ prop-P : MereProposition{ℓ}(P) ⦄ ⦃ prop-Q : MereProposition{ℓ}(Q) ⦄ where
  propositional-extensionality : Path P Q ↔ (P ↔ Q)
  propositional-extensionality = intro l (sub₂(Path)(_↔_) ⦃ Path-sub-of-reflexive ⦄) where
    l : Path P Q ← (P ↔ Q)
    l pq = type-extensionality $ₗ ([∃]-intro pq ⦃ intro ⦄) where
      instance
        invₗ : Inverseₗ(pq $ₗ_)(pq $ᵣ_)
        invₗ = intro(uniqueness(Q))
      instance
        invᵣ : Inverseᵣ(pq $ₗ_)(pq $ᵣ_)
        invᵣ = intro(uniqueness(P))
