module Numeral.Finite.Conversions where

import      Lvl
open import Data using (Empty ; Unit ; <>)
open import Data.Boolean using (Bool ; 𝐹 ; 𝑇)
open import Data.Tuple using (_,_)
open import Logic.Propositional using (_↔_)
open import Numeral.Finite
open import Numeral.Natural
open import Syntax.Number

private variable ℓ : Lvl.Level

empty : 𝕟(0) ↔ Empty{ℓ}
empty = (\()) , (\())

unit : 𝕟(1) ↔ Unit{ℓ}
unit = (\{<> → 0}) , (\{𝟎 → <>})

bool : 𝕟(2) ↔ Bool
bool = (\{𝐹 → 0 ; 𝑇 → 1}) , (\{𝟎 → 𝐹 ; (𝐒(𝟎)) → 𝑇})
