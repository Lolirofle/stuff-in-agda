import      Lvl
open import Type

module Structure.Logic.Constructive.Functions {ℓₒ} (Domain : Type{ℓₒ}) where

private
  module Meta where
    open import Numeral.FiniteStrict           public
    open import Numeral.Natural                public

-- The type of a function. Functions on the domain in the meta-logic.
Function : Type{_}
Function = (Domain → Domain)

BinaryOperator : Type{_}
BinaryOperator = (Domain → Domain → Domain)

Tuple : Meta.ℕ → Type{_}
Tuple(n) = Meta.𝕟(n) → Domain

Sequence : Type{_}
Sequence = Meta.ℕ → Domain
