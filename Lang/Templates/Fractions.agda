open import Syntax.Number
open import Type

module Lang.Templates.Fractions {ℓ₁ ℓ₂ ℓ₃}
  {A : Type{ℓ₁}} {B : Type{ℓ₂}} {C : A → B → Type{ℓ₃}}
  (_/_ : (a : A) → (b : B) → C a b)
  ⦃ num-a : InfiniteNumeral(A) ⦄
  ⦃ num-b : InfiniteNumeral(B) ⦄
  where

open import Data

¼ = 1 / 4
½ = 1 / 2
¾ = 3 / 4
⅐ = 1 / 7
⅑ = 1 / 9
⅒ = 1 / 10
⅓ = 1 / 3
⅔ = 2 / 3
⅕ = 1 / 5
⅖ = 2 / 5
⅗ = 3 / 5
⅘ = 4 / 5
⅙ = 1 / 6
⅚ = 5 / 6
⅛ = 1 / 8
⅜ = 3 / 8
⅝ = 5 / 8
⅞ = 7 / 8
