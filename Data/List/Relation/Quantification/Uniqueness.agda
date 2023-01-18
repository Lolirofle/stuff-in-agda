module Data.List.Relation.Quantification.Uniqueness where

import      Lvl
open import Data.List
open import Data.List.Relation.Quantification
import      Data.List.Relation.Quantification.Existential.Functions as ∃ₗᵢₛₜ
open import Functional
open import Logic
open import Structure.Relator.Equivalence.Proofs.On₂
open import Structure.Setoid
open import Type
open import Type.Identity
open import Type.Identity.Proofs
open import Type.Properties.Singleton

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

ExistsUniqueElement : (T → Stmt{ℓ}) → List(T) → Stmt
ExistsUniqueElement P l = IsUnit(ExistsElement(P)(l)) ⦃ intro (Id on₂ ∃ₗᵢₛₜ.index) ⦃ on₂-equivalence ⦃ Id-equivalence ⦄ ⦄ ⦄

∃!ₗᵢₛₜ : List(T) → (T → Stmt{ℓ}) → Stmt
∃!ₗᵢₛₜ(l) P = ExistsUniqueElement P l

_∈!_ : T → List(T) → Stmt
_∈!_ = ExistsUniqueElement ∘ Id
