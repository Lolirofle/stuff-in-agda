module FunctionalML where

open import Numeral.Finite
open import Numeral.Natural

data Value : ℕ → Set
data Expression : ℕ → Set

data Value where
  const : ∀{n} → ℕ → Value n
  var : ∀{n} → 𝕟(n) → Value n
  y-combinator : ∀{n} → Value n
  func : ∀{n} → Value(𝐒 n) → Value n

data Expression where
  val : ∀{n} → Value n → Expression n
  apply : ∀{n} → Expression n → Expression n

