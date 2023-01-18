module Numeral.Sign where

import      Lvl
open import Type

-- The set of plus or minus sign
data Sign : Type{Lvl.𝟎} where
  ➕ : Sign
  ➖ : Sign

elim : ∀{ℓ}{P : Sign → Type{ℓ}} → P(➖) → P(➕) → ((s : Sign) → P(s))
elim neg pos ➖ = neg
elim neg pos ➕ = pos
