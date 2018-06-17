module Numeral.Natural.Relation.Computability where

import      Lvl
open import Data.Boolean
open import Data.Boolean.AsSet
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Logic.Computability.Binary
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons

instance
  postulate [≡]-computable : ComputablyDecidable{ℕ}(_≡_)

instance
  postulate [≢]-computable : ComputablyDecidable{ℕ}(_≢_)
