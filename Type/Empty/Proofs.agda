module Type.Empty.Proofs where

open import Data
open import Logic.Propositional
import      Lvl
open import Type.Empty
open import Type

-- A type is never inhabited and empty at the same time.
notInhabitedAndEmpty : ∀{ℓ}{T : Type{ℓ}} → (◊ T) → IsEmpty{ℓ}(T) → ⊥
notInhabitedAndEmpty (intro ⦃ obj ⦄) (intro empty) with empty{Empty} (obj)
... | ()
