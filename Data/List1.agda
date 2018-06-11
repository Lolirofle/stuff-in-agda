module Data.List1 where

open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data hiding (empty)
open import Functional
open import Data.List
open import Numeral.Natural
open import Type

-- A non-empty list
data List1 {ℓ} (T : Type{ℓ}) : Type{ℓ} where
  _⊰_ : T → List(T) → List1(T)
