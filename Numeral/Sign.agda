module Numeral.Sign where

-- The set of plus or minus sign
data +|− : Set where
  + : (+|−)
  − : (+|−)

−|+ = +|−

-- The set of signs: plus, minus and neutral
data +|0|− : Set where
  +   : (+|0|−)
  [0] : (+|0|−)
  −   : (+|0|−)

−|0|+ = +|0|−

zeroable : (+|−) → (+|0|−)
zeroable (+) = (+)
zeroable (−) = (−)
