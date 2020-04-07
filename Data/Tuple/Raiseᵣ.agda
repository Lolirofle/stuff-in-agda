module Data.Tuple.Raiseᵣ where

open import Data
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Numeral.Natural
open import Type

_^_ : ∀{ℓ} → Type{ℓ} → ℕ → Type{ℓ}
_^_ type 0      = Unit
_^_ type 1      = type
_^_ type (𝐒(𝐒(n))) = type ⨯ (type ^ 𝐒(n))
