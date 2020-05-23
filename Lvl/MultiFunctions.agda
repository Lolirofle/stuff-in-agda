module Lvl.MultiFunctions where

open import Data
open import Data.Tuple
open import Data.Tuple.Raise
import      Data.Tuple.Raiseᵣ.Functions as Raise
open import Lvl

-- The maximum level of a tuple list of levels.
⨆ : ∀{n} → (Level ^ n) → Level
⨆ = Raise.foldᵣ(_⊔_) 𝟎
