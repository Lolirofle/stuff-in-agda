module Numeral.Rational.CalkinWilf where

open import Numeral.Natural as ℕ
import Numeral.Natural.Oper as ℕ

data _/_ : ℕ → ℕ → Set where
  [/]-intro : (1 / 1)
  [/]-left  : ∀{x y} → (x / y) → (x / (x + y))
  [/]-right : ∀{x y} → (x / y) → ((x + y) / y)

module _/_ where
  -- _+_ : (a₁ / b₁) → (a₂ / b₂) → 
  -- _⋅_ : (a₁ / b₁) → (a₂ / b₂) → 

data ℚ : Set where
  𝟎  : ℚ
  −_ : ∀{x y} → (x / y) → ℚ
  +_ : ∀{x y} → (x / y) → ℚ

{-
a₁/(a₁+b₁)
(a₂+b₂)/b₂
-}
