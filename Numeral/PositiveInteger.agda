module Numeral.PositiveInteger where

import Lvl
open import Syntax.Number
open import Data.Boolean.Stmt
open import Functional
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural as ℕ using (ℕ)
open import Relator.Equals
open import Type

ℕ₊ = ℕ
open import Numeral.Natural using (𝐒) renaming (𝟎 to 𝟏) public

toℕ : ℕ₊ → ℕ
toℕ 𝟏     = ℕ.𝐒(ℕ.𝟎)
toℕ(𝐒(n)) = ℕ.𝐒(toℕ n)

fromℕ : (n : ℕ) → ⦃ _ : IsTrue(positive?(n)) ⦄ → ℕ₊
fromℕ (ℕ.𝟎)         ⦃ ⦄
fromℕ (ℕ.𝐒(ℕ.𝟎))    ⦃ _ ⦄ = 𝟏
fromℕ (ℕ.𝐒(ℕ.𝐒(x))) ⦃ p ⦄ = 𝐒(fromℕ (ℕ.𝐒(x)) ⦃ p ⦄)

𝐒ₙ : ℕ → ℕ₊
𝐒ₙ = id

𝐏ₙ : ℕ₊ → ℕ
𝐏ₙ 𝟏     = ℕ.𝟎
𝐏ₙ(𝐒(n)) = ℕ.𝐒(𝐏ₙ(n))

ℕ₊-is-ℕ : ℕ₊ ≡ ℕ
ℕ₊-is-ℕ = [≡]-intro

instance
  ℕ₊-numeral : Numeral(ℕ₊) (n ↦ IsTrue(positive?(n)))
  num ⦃ ℕ₊-numeral ⦄ n = fromℕ n
