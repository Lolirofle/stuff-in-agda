module Numeral.Sign.Oper0 where

open import Numeral.Sign

-- Negation
−_ : (+|0|−) → (+|0|−)
− (➕) = (➖)
− (𝟎) = (𝟎)
− (➖) = (➕)

-- Bounded addition
_+_ : (+|0|−) → (+|0|−) → (+|0|−)
(➕) + (➕) = (➕)
(➕) + (➖) = (𝟎)
(➕) + (𝟎) = (➕)
(➖) + (➕) = (𝟎)
(➖) + (➖) = (➖)
(➖) + (𝟎) = (➖)
(𝟎) + (➕) = (➕)
(𝟎) + (➖) = (➖)
(𝟎) + (𝟎) = (𝟎)

-- Multiplication
_⨯_ : (+|0|−) → (+|0|−) → (+|0|−)
(➕) ⨯ (➕) = (➕)
(➕) ⨯ (➖) = (➖)
(➕) ⨯ (𝟎) = (𝟎)
(➖) ⨯ (➕) = (➖)
(➖) ⨯ (➖) = (➕)
(➖) ⨯ (𝟎) = (𝟎)
(𝟎) ⨯ (➕) = (𝟎)
(𝟎) ⨯ (➖) = (𝟎)
(𝟎) ⨯ (𝟎) = (𝟎)
