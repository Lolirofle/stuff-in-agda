module Operator.Equals {lvl} where

import      Level as Lvl
open import Boolean
open import Functional
open import Type{lvl}

-- Type class for run-time checking of equality
record Eq(T : Type) : Type where
  infixl 100 _==_
  field
    _==_ : T → T → Bool
open Eq {{...}} public
