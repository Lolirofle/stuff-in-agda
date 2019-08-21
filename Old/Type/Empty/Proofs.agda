module Type.Empty.Proofs where

open import Data
import      Lvl
open import Type.Empty
open import Logic.Propositional

-- A type is never inhabited and empty at the same time.
notInhabitedAndEmpty : ∀{ℓ₁ ℓ₂}{T : Set(ℓ₁)} → (◊ T) → IsEmpty{ℓ₁}{ℓ₂}(T) → ⊥
notInhabitedAndEmpty (◊.intro ⦃ obj ⦄) (IsEmpty.intro empty) =
  empty{Empty} (obj)
