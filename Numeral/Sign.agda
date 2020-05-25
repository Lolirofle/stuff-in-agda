module Numeral.Sign where

import      Lvl
open import Type

-- The set of plus or minus sign
data +|− : Type{Lvl.𝟎} where
  ➕ : (+|−)
  ➖ : (+|−)

−|+ = +|−

-- The set of signs: plus, minus and neutral
data +|0|− : Type{Lvl.𝟎} where
  ➕ : (+|0|−)
  𝟎 : (+|0|−)
  ➖ : (+|0|−)

−|0|+ = +|0|−

zeroable : (+|−) → (+|0|−)
zeroable (➕) = (➕)
zeroable (➖) = (➖)
