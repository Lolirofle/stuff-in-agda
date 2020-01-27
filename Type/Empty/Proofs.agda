module Type.Empty.Proofs where

open import Data
import      Lvl
open import Type.Empty
open import Logic.Propositional

-- A type is never inhabited and empty at the same time.
notInhabitedAndEmpty : ∀{ℓ}{T : Set(ℓ)} → (◊ T) → IsEmpty{ℓ}(T) → ⊥
notInhabitedAndEmpty (intro ⦃ obj ⦄) (intro empty) with empty{Empty} (obj)
... | ()
