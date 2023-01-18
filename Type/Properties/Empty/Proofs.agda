module Type.Properties.Empty.Proofs where

open import BidirectionalFunction using (_$ₗ_ ; _$ᵣ_)
open import Data as Data using (Empty)
open import Functional
open import Logic.Propositional
import      Lvl
open import Type.Properties.Empty
open import Type

private variable ℓ ℓₜ : Lvl.Level
private variable A B T : Type{ℓ}

-- A type being empty is equivalent to the existence of a function from the type to the empty type of any universe level.
empty-by-Empty : IsEmpty{ℓₜ}(T) ↔ (T → Empty{ℓ})
empty-by-Empty = [↔]-intro
  (intro ∘ (Data.empty ∘_))
  (e ↦ Data.empty ∘ empty ⦃ e ⦄)

empty-by-negation : IsEmpty{ℓₜ}(T) ↔ (¬ T)
empty-by-negation = empty-by-Empty

emptyAny : ⦃ IsEmpty{ℓₜ}(A) ⦄ → (A → B)
emptyAny ⦃ e ⦄ = empty ⦃ empty-by-negation $ₗ (empty-by-negation $ᵣ e) ⦄

empty-by-function : (f : A → B) → (IsEmpty{ℓₜ}(A) ← IsEmpty{ℓₜ}(B))
empty-by-function f (intro empty-B) = intro(empty-B ∘ f)
