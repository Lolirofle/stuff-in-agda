module Numeral.Sign where

import      Lvl
open import Type

-- The set of plus or minus sign
data +|− : Type{Lvl.𝟎} where
  ➕ : (+|−)
  ➖ : (+|−)

−|+ = +|−

elim₂ : ∀{ℓ}{P : (+|−) → Type{ℓ}} → P(➖) → P(➕) → ((s : (+|−)) → P(s))
elim₂ neg pos ➖ = neg
elim₂ neg pos ➕ = pos

-- The set of signs: plus, minus and neutral
data +|0|− : Type{Lvl.𝟎} where
  ➕ : (+|0|−)
  𝟎 : (+|0|−)
  ➖ : (+|0|−)

−|0|+ = +|0|−

elim₃ : ∀{ℓ}{P : (+|0|−) → Type{ℓ}} → P(➖) → P(𝟎) → P(➕) → ((s : (+|0|−)) → P(s))
elim₃ neg zero pos ➖ = neg
elim₃ neg zero pos 𝟎 = zero
elim₃ neg zero pos ➕ = pos

zeroable : (+|−) → (+|0|−)
zeroable (➕) = (➕)
zeroable (➖) = (➖)
