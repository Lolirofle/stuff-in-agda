module Data.Option.Equiv where

import      Lvl
open import Data.Option
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ ℓₑₐ : Lvl.Level
private variable A : Type{ℓ}

record Extensionality ⦃ equiv-A : Equiv{ℓₑₐ}(A) ⦄ (equiv : Equiv{ℓₑ}(Option(A))) : Type{Lvl.of(A) Lvl.⊔ ℓₑₐ Lvl.⊔ ℓₑ} where
  constructor intro
  private instance _ = equiv
  field
    ⦃ Some-function ⦄ : Function Some
    ⦃ Some-injective ⦄ : Injective Some
    cases-inequality : ∀{x : A} → (None ≢ Some(x))
open Extensionality ⦃ … ⦄ public
