module Typeω.Dependent.Sigma where

import      Lvl
open import Type

record Σ (A : Typeω) (B : A → Typeω) : Typeω where
  eta-equality
  constructor intro
  field
    left  : A
    right : B(left)
