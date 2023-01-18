module Structure.Set.Equiv where

import      Lvl
open import Structure.Set.Relators using (SetEqualityRelation)
open import Structure.Setoid hiding (_≡_)
open import Type

private variable ℓ ℓₗ ℓₑ : Lvl.Level
private variable E S : Type{ℓ}

SetExtensionality : (E → S → Type{ℓₗ}) → Equiv{ℓₑ}(S) → Type
SetExtensionality(_∈_) equiv = SetEqualityRelation(_∈_)(_∈_)(Equiv._≡_ equiv)
