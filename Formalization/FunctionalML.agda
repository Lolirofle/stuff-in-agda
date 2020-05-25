module Formalization.FunctionML where

import      Lvl
open import Numeral.Finite
open import Numeral.Natural
open import Type{Lvl.𝟎}

data Value : ℕ → Type
data Expression : ℕ → Type

data Value where
  const : ∀{n} → ℕ → Value n
  var : ∀{n} → 𝕟(n) → Value n
  y-combinator : ∀{n} → Value n
  func : ∀{n} → Value(𝐒 n) → Value n

data Expression where
  val : ∀{n} → Value n → Expression n
  apply : ∀{n} → Expression n → Expression n

