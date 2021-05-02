module Operator.Equals {ℓ ℓₑ} where

open import Data.Boolean
open import Functional
open import Logic
open import Structure.Setoid
open import Type.Properties.Decidable
open import Type

EquivDecider : {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → (_≡?_ : T → T → Bool) → Stmt
EquivDecider(_≡?_) = Decider(2)(_≡_)(_≡?_)

EquivDecidable : (T : Type{ℓ}) ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → Stmt
EquivDecidable(T) = Decidable(2)(_≡_)

module _ {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ _ : EquivDecidable(T) ⦄ where
  _==_ : (T → T → Bool)
  _==_ = decide(2)(_≡_)

  _!=_ : (T → T → Bool)
  _!=_ = not ∘₂ (_==_)
