module Data.Tuple.RaiseTypeᵣ where

open import Data
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Raise
open import Lvl using (Level)
open import Lvl.MultiFunctions
open import Numeral.Natural
open import Type

-- A list of types of different levels.
-- TODO: Is it possible to define this by using (_^_)?
Types : ∀{n} → (ℓ𝓈 : (Level ^ n)) → Type{Lvl.𝐒(⨆{n} ℓ𝓈)}
Types {0}       _       = Unit
Types {1}       ℓ       = Type{ℓ}
Types {𝐒(𝐒(n))} (ℓ , ℓ𝓈) = Type{ℓ} ⨯ Types{𝐒(n)}(ℓ𝓈)
