module Lang.Irrelevance.Squash where

open import Lang.Irrelevance.Convertable
import      Lvl
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₚ : Lvl.Level
private variable A B C P Q R T : Type{ℓ}
private variable f g : A → B

-- Propositional squashing using the irrelevant universe.
record Squash(T : Type{ℓ}) : Type{ℓ} where
  constructor intro
  field .prop : T
  obj : ⦃ Convertable(T) ⦄ → T
  obj = convert(T) prop

open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Type.Properties.MereProposition

instance
  Squash-mereProposition : MereProposition(Squash(T))
  Squash-mereProposition = intro [≡]-intro
