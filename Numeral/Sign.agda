module Numeral.Sign where

data +|− : Set where
  + : (+|−)
  − : (+|−)

−|+ = +|−

data +|0|− : Set where
  + : (+|0|−)
  [0] : (+|0|−)
  − : (+|0|−)

−|0|+ = +|0|−

zeroable : (+|−) → (+|0|−)
zeroable (+) = (+)
zeroable (−) = (−)
