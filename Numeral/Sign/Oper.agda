module Numeral.Sign.Oper where

open import Numeral.Sign

-- Negation
−_ : (+|−) → (+|−)
− (➕) = (➖)
− (➖) = (➕)

-- Bounded addition
_+_ : (+|−) → (+|−) → (+|0|−)
(➕) + (➕) = (➕)
(➖) + (➖) = (➖)
(➕) + (➖) = (𝟎)
(➖) + (➕) = (𝟎)

-- Multiplication
_⨯_ : (+|−) → (+|−) → (+|−)
(➕) ⨯ (➕) = (➕)
(➖) ⨯ (➖) = (➕)
(➕) ⨯ (➖) = (➖)
(➖) ⨯ (➕) = (➖)

-- Division
_/_ = _⨯_
