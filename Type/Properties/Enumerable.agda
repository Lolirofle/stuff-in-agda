module Type.Properties.Enumerable where

import      Lvl
open import Numeral.Natural
open import Structure.Function.Domain
open import Structure.Setoid
open import Type
open import Type.Identity.Proofs

private variable ℓ ℓₑ : Lvl.Level

record Enumerable (T : Type{ℓ}) ⦃ equiv : Equiv{ℓₑ}(T) ⦄ : Type{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    enum : T → ℕ
    ⦃ enum-injective ⦄ : Injective ⦃ equiv ⦄ ⦃ Id-equiv ⦄ (enum)
open Enumerable ⦃ … ⦄ using (enum) public
