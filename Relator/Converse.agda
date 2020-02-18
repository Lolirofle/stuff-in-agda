open import Type

module Relator.Converse {ℓ₁ ℓ₂} {T : Type{ℓ₁}} (_▫_ : T → T → Type{ℓ₂}) where

import      Lvl
open import Functional

Converse : T → T → Type{ℓ₂}
Converse = swap(_▫_)
