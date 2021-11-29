module Structure.Setoid.Universal where

open import Data
open import Functional
open import Logic.Predicate
import      Lvl
open import Structure.Setoid
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}

-- The equivalence relation of a binary relation relating every object of a type.
universal-equiv : Equiv{ℓₑ}(T)
Equiv._≡_                                   universal-equiv  = const(const Unit)
Equivalence.reflexivity  (Equiv.equivalence universal-equiv) = intro <>
Equivalence.symmetry     (Equiv.equivalence universal-equiv) = intro(const <>)
Equivalence.transitivity (Equiv.equivalence universal-equiv) = intro(const(const <>))

universal-setoid : Type{ℓ} → Setoid{ℓₑ}
universal-setoid T = [∃]-intro T ⦃ universal-equiv ⦄
