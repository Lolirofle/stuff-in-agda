open import Type
open import Structure.Setoid renaming (_≡_ to _≡ₑ_)

-- Finite sets represented by lists
module Data.List.Relation.Membership {ℓ ℓₑ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T)⦄ where

open import Data.List
open import Data.List.Relation.Quantification using (ExistsElement ; ExistsUniqueElement)
open import Functional
open import Logic

_∈_ : T → List(T) → Stmt
_∈_ = ExistsElement ∘ (_≡ₑ_)
module _∈_ where
  pattern use  {x}{l} px = ExistsElement.•_ {x = x}{l = l} px
  pattern skip {x}{l} el = ExistsElement.⊰_ {l = l}{x = x} el

open _∈_ public
open import Relator.Sets(_∈_) public

_∈!_ : T → List(T) → Stmt
_∈!_ = ExistsUniqueElement ∘ (_≡ₑ_)
