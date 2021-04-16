module Formalization.PredicateLogic.Signature where

import      Lvl
open import Numeral.Natural
open import Type

-- A signature consists of a countable family of constant/function and relation symbols.
-- `Prop(n)` should be interpreted as the indices for relations of arity `n`.
-- `Obj(n)` should be interpreted as the indices for functions of arity `n` (constants if `n = 0`).
record Signature : Typeω where
  constructor intro
  field
    {ℓₚ} : Lvl.Level
    Prop : ℕ → Type{ℓₚ}
    {ℓₒ} : Lvl.Level
    Obj : ℕ → Type{ℓₒ}
