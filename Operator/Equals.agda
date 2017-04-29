module Operator.Equals where

import      Level as Lvl
open import Boolean
open import Functional

record Eq{lvl : Lvl.Level}(T : Set(lvl)) : Set(lvl) where
  infixl 100 _==_
  field
    _==_ : T → T → Bool
open Eq {{...}} public
