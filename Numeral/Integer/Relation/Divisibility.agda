module Numeral.Integer.Relation.Divisibility where

open import Functional
open import Logic.Propositional
import      Numeral.Natural.Relation.Divisibility as ℕ
open import Numeral.Integer
open import Type

_∣_ = (ℕ._∣_) on₂ absₙ
_∤_ = (¬_) ∘₂ (_∣_)
