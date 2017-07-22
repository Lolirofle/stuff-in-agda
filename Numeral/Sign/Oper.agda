module Numeral.Sign.Oper where

open import Numeral.Sign

-- Negation
−_ : (+|−) → (+|−)
− (+) = (−)
− (−) = (+)

-- Multiplication
_⋅_ : (+|−) → (+|−) → (+|−)
(+) ⋅ (+) = (+)
(−) ⋅ (−) = (+)
(+) ⋅ (−) = (−)
(−) ⋅ (+) = (−)

-- Division
_/_ = _⋅_
