module Numeral.Charge.Oper where

open import Numeral.Charge

-- Negation
−_ : Charge → Charge
− (➕) = (➖)
− (𝟎) = (𝟎)
− (➖) = (➕)

-- Bounded addition
_+_ : Charge → Charge → Charge
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
_⨯_ : Charge → Charge → Charge
(➕) ⨯ (➕) = (➕)
(➕) ⨯ (➖) = (➖)
(➕) ⨯ (𝟎) = (𝟎)
(➖) ⨯ (➕) = (➖)
(➖) ⨯ (➖) = (➕)
(➖) ⨯ (𝟎) = (𝟎)
(𝟎) ⨯ (➕) = (𝟎)
(𝟎) ⨯ (➖) = (𝟎)
(𝟎) ⨯ (𝟎) = (𝟎)

_⋚_ : Charge → Charge → Charge
➕ ⋚ 𝟎 = ➕
➕ ⋚ ➖ = ➕
𝟎 ⋚ ➖ = ➕
➕ ⋚ ➕ = 𝟎
𝟎 ⋚ 𝟎 = 𝟎
➖ ⋚ ➖ = 𝟎
𝟎 ⋚ ➕ = ➖
➖ ⋚ ➕ = ➖
➖ ⋚ 𝟎 = ➖
