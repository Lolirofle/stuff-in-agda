module Numeral.Integer.Relation where

open import Functional
open import Numeral.Natural.Relation
open import Numeral.Integer
open import Type

NonZero : ℤ → Type
NonZero = Positive ∘ absₙ
