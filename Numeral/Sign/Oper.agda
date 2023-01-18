module Numeral.Sign.Oper where

open import Data.Boolean
open import Numeral.Charge
open import Numeral.Sign

-- Negation
−_ : Sign → Sign
− (➕) = (➖)
− (➖) = (➕)

-- Addition
_+_ : Sign → Sign → Charge
(➕) + (➕) = (➕)
(➖) + (➖) = (➖)
(➕) + (➖) = (𝟎)
(➖) + (➕) = (𝟎)

-- Multiplication
_⨯_ : Sign → Sign → Sign
(➕) ⨯ (➕) = (➕)
(➖) ⨯ (➖) = (➕)
(➕) ⨯ (➖) = (➖)
(➖) ⨯ (➕) = (➖)

_⋚_ : Sign → Sign → Charge
➕ ⋚ ➕ = 𝟎
➕ ⋚ ➖ = ➕
➖ ⋚ ➕ = ➖
➖ ⋚ ➖ = 𝟎

zeroable : Sign → Charge
zeroable (➕) = (➕)
zeroable (➖) = (➖)
