module Numeral.Rational where

open import Data
open import Data.Boolean.Stmt
import      Lvl
open import Numeral.Integer as ℤ using (ℤ)
open import Numeral.Natural as ℕ using (ℕ)
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Relation
open import Type

record ℚ : Type{Lvl.𝟎} where
  constructor _/ₙ_
  eta-equality
  field
    numerator   : ℤ
    denominator : ℕ
    ⦃ .coprime ⦄ : IsTrue(gcd (ℤ.absₙ numerator) denominator ≡? 1)
    ⦃ .positive ⦄ : Positive(denominator)
𝟎 : ℚ
𝟎 = ℤ.𝟎 /ₙ ℕ.𝟏

𝟏 : ℚ
𝟏 = ℤ.𝟏 /ₙ ℕ.𝟏
