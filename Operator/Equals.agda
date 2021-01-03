module Operator.Equals {ℓ ℓₑ} where

open import Data.Boolean
open import Logic
open import Structure.Setoid
open import Type.Properties.Decidable
open import Type

DecidableEquiv : (T : Type{ℓ}) ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → Stmt
DecidableEquiv(T) = Decidable(2)(_≡_)

_==_ : ∀{T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ _ : DecidableEquiv(T) ⦄ → (T → T → Bool)
_==_ = decide(2)(_≡_)
