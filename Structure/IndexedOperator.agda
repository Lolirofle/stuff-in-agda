module Structure.IndexedOperator where

open import Data
open import Data.Tuple using (_,_)
open import Data.Tuple.Raiseᵣ
import      Lvl
open import Numeral.Natural
open import Type

private variable ℓ ℓₒ ℓₘ : Lvl.Level
private variable I : Type{ℓₒ}

module _ (T : I → Type{ℓₘ}) where
  IndexedOperator : (n : ℕ) → (I ^ n) → Type{ℓₘ}
  IndexedOperator 0         <>       = Unit
  IndexedOperator 1         i        = T(i)
  IndexedOperator (𝐒(𝐒(n))) (i , is) = T(i) → IndexedOperator(𝐒(n)) is
