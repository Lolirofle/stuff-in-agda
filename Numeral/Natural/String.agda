module Numeral.Natural.String where

open import Numeral.Natural
open import String

module Primitives where
  primitive primShowNat : ℕ → String

instance
  ℕ-stringRepr : StringRepr(ℕ)
  StringRepr.string ℕ-stringRepr = Primitives.primShowNat
