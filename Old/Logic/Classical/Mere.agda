module Logic.Classical.Mere {ℓ} where

import      Lvl
open import Data hiding (empty)
open import Relator.Bijection{ℓ}{ℓ}
open import Relator.Equals{ℓ}{ℓ}
open import Type{ℓ}

Mere : Type → Type
Mere(T) = (∀{x y : T} → (x ≡ y))

module Theorems where
  empty : Mere(Empty)
  empty {}

  unit : Mere(Unit)
  unit {<>} {<>} = [≡]-intro

  -- proof-implies-unit : ∀{T} → Mere(T) → T → ?
  -- proof-implies-unit ([≡]-intro) (x) = ?
