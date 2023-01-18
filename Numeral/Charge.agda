module Numeral.Charge where

open import Data.Boolean
import      Lvl
open import Type

-- The set of signs: plus, minus and neutral
data Charge : Type{Lvl.𝟎} where
  ➕ : Charge
  𝟎 : Charge
  ➖ : Charge

elim₃ : ∀{ℓ}{P : Charge → Type{ℓ}} → P(➖) → P(𝟎) → P(➕) → ((s : Charge) → P(s))
elim₃ neg zero pos ➖ = neg
elim₃ neg zero pos 𝟎 = zero
elim₃ neg zero pos ➕ = pos

isPositive : Charge → Bool
isPositive = elim₃ 𝐹 𝐹 𝑇

isNeutral : Charge → Bool
isNeutral = elim₃ 𝐹 𝑇 𝐹

isNegative : Charge → Bool
isNegative = elim₃ 𝑇 𝐹 𝐹

isPositive₌ : Charge → Bool
isPositive₌ = elim₃ 𝐹 𝑇 𝑇

isNegative₌ : Charge → Bool
isNegative₌ = elim₃ 𝑇 𝑇 𝐹
