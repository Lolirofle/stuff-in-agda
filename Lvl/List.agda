module Lvl.List where

open import Data
open import Data.Tuple
open import Data.Tuple.Raise
import      Data.Tuple.Raiseᵣ.Functions as Raise
open import Lvl using (Level)
open import Numeral.Natural

⨆ : ∀{n} → (Level ^ n) → Level
⨆ = Raise.foldᵣ(Lvl._⊔_) Lvl.𝟎
