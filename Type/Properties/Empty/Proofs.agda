module Type.Properties.Empty.Proofs where

open import Data as Data using (Empty)
open import Functional
open import Logic.Propositional
import      Lvl
open import Type.Properties.Empty
open import Type

private variable ℓ ℓₜ : Lvl.Level
private variable A B T : Type{ℓ}

-- A type being empty is equivalent to the existence of a function from the type to the empty type of any universe level.
empty-negation-eq : IsEmpty{ℓₜ}(T) ↔ (T → Empty{ℓ})
empty-negation-eq = [↔]-intro
  (intro ∘ (Data.empty ∘_))
  (e ↦ Data.empty ∘ empty ⦃ e ⦄)

empty-by-function : (f : A → B) → (IsEmpty{ℓₜ}(A) ← IsEmpty{ℓₜ}(B))
empty-by-function f (intro empty-B) = intro(empty-B ∘ f)
