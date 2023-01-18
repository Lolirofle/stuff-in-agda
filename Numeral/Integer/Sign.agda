module Numeral.Integer.Sign where

open import Data.Boolean
open import Functional
open import Numeral.Charge as Charge using (Charge ; ➕ ; ➖)
open import Numeral.Natural as ℕ
open import Numeral.Integer as ℤ
open import Numeral.Sign

sign : ℤ → Sign
sign(+ₙ _) = ➕
sign(−𝐒ₙ _) = ➖

sign0 : ℤ → Charge
sign0(ℤ.𝟎) = Charge.𝟎
sign0(+𝐒ₙ _) = ➕
sign0(−𝐒ₙ _) = ➖

signum0 : ℤ → ℤ
signum0(ℤ.𝟎) = ℤ.𝟎
signum0(+𝐒ₙ _) = +𝐒ₙ(ℕ.𝟎)
signum0(−𝐒ₙ _) = −𝐒ₙ(ℕ.𝟎)

isPositive : ℤ → Bool
isPositive = Charge.isPositive ∘ sign0

isZero : ℤ → Bool
isZero = Charge.isNeutral ∘ sign0

isNegative : ℤ → Bool
isNegative = Charge.isNegative ∘ sign0

isPositive₌ : ℤ → Bool
isPositive₌ = Charge.isPositive₌ ∘ sign0

isNegative₌ : ℤ → Bool
isNegative₌ = Charge.isNegative₌ ∘ sign0
