module Structure.Relator.Equivalence.Proofs where

import      Lvl
open import Functional
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties.Proofs
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable _▫_ : T → T → Type{ℓ}
private variable f : A → B

on₂-equivalence : ⦃ eq : Equivalence(_▫_) ⦄ → Equivalence((_▫_) on₂ f)
Equivalence.reflexivity  (on₂-equivalence {_▫_ = _▫_}) = on₂-reflexivity
Equivalence.symmetry     (on₂-equivalence {_▫_ = _▫_}) = on₂-symmetry
Equivalence.transitivity (on₂-equivalence {_▫_ = _▫_}) = on₂-transitivity
