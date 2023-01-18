module Structure.Setoid.On₂ where

open import Functional
open import Functional.Instance
import      Lvl
open import Structure.Relator.Equivalence.Proofs.On₂
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable A B : Type{ℓ}

on₂-equiv : (A ← B) → ⦃ Equiv{ℓₑ}(A) ⦄ → Equiv(B)
Equiv._≡_         (on₂-equiv f) = (_≡_) on₂ f
Equiv.equivalence (on₂-equiv f) = on₂-equivalence {_▫_ = _≡_}{f = f} ⦃ Equiv.equivalence infer ⦄
