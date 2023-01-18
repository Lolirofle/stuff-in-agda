module Lvl.Up.Equiv where

open import Lvl
open import Structure.Function
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ ℓₑₗ : Lvl.Level
private variable T : Type{ℓ}

record LvlUpExtensionality ⦃ equiv : Equiv{ℓₑ}(T) ⦄ (equiv-LvlUp : Equiv{ℓₑₗ}(Lvl.Up{ℓ} T)) : Type{ℓₑ ⊔ ℓ ⊔ Lvl.of(T) ⊔ ℓₑₗ} where
  constructor intro
  instance _ = equiv-LvlUp
  field
    ⦃ up-function ⦄  : Function(Lvl.up)
    ⦃ obj-function ⦄ : Function(Lvl.Up.obj)
