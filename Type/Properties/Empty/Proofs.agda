module Type.Properties.Empty.Proofs where

import      Data.Tuple
open import Data
open import Functional
open import Logic.Propositional
import      Lvl
open import Type.Properties.Inhabited
open import Type.Properties.Empty
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

-- A type is never inhabited and empty at the same time.
notInhabitedAndEmpty : (◊ T) → IsEmpty(T) → ⊥
notInhabitedAndEmpty (intro ⦃ obj ⦄) (intro empty) with () ← empty{Empty} (obj)

-- A type being empty is equivalent to the existence of a function from the type to the empty type of any universe level.
empty-negation-eq : IsEmpty(T) ↔ (T → Empty{ℓ})
IsEmpty.empty (Data.Tuple.left empty-negation-eq nt) = empty ∘ nt
Data.Tuple.right empty-negation-eq (intro e) t with () ← e {Empty} t
