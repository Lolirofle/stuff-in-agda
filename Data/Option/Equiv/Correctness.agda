module Data.Option.Equiv.Correctness where

import      Lvl
open import Data.Option
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Setoid.WithLvl
open import Type

private variable ℓ ℓₑ ℓₑₐ : Lvl.Level
private variable A : Type{ℓ}

record Correctness ⦃ equiv-A : Equiv{ℓₑₐ}(A) ⦄ (equiv : Equiv{ℓₑ}(Option(A))) : Type{Lvl.of(A) Lvl.⊔ ℓₑₐ Lvl.⊔ ℓₑ} where
  constructor intro
  private instance _ = equiv
  field
    ⦃ Some-function ⦄ : Function Some
    ⦃ Some-injective ⦄ : Injective Some
    cases-inequality : ∀{x : A} → (None ≢ Some(x))
