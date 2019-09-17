open import Type

module Operator.Equals {ℓ} where

open import Data.Boolean
open import Logic
open import Logic.Computability.Binary
open import Relator.Equals

BoolEquality : (T : Type{ℓ}) → Stmt
BoolEquality(T) = ComputablyDecidable {X = T} (_≡_)

_==_ : ∀{T : Type{ℓ}} → ⦃ _ : BoolEquality(T) ⦄ → T → T → Bool
_==_ = ComputablyDecidable.decide(_≡_)
