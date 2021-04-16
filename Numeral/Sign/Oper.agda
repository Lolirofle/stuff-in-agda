module Numeral.Sign.Oper where

open import Data.Boolean
open import Numeral.Sign

-- Negation
−_ : (+|−) → (+|−)
− (➕) = (➖)
− (➖) = (➕)

-- Addition
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

_⋚_ : (+|−) → (+|−) → (+|0|−)
➕ ⋚ ➕ = 𝟎
➕ ⋚ ➖ = ➕
➖ ⋚ ➕ = ➖
➖ ⋚ ➖ = 𝟎
