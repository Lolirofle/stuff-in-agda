module Formalization.LambdaCalculus.Semantics where

open import Data
open import Formalization.LambdaCalculus
open import Syntax.Number
open import Type

-- A value in the language of lambda calculus is a irreducible term by a standard reduction definition.
-- It can also be defined as terms that are lambda abstractions because an application of a lambda is supposed to be β-reducible.
data Value : Expression → Type{0} where
  instance abs : ∀{body : Term(1)} → Value(Abstract body)
