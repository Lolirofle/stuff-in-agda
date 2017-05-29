module Operator.Equals {ℓ} where

import      Level as Lvl
open import Boolean
open import Functional
open import Relator.Equals{ℓ}{ℓ}
open import Type{ℓ}

-- Type class for run-time checking of equality
record Equals(T : Type) : Type where
  infixl 100 _==_
  field
    _==_ : T → T → Bool
  field
    {completeness} : ∀{a b : T} → (a ≡ b) → (a == b ≡ 𝑇)
open Equals {{...}} using (_==_) public
