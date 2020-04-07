module Numeral.PositiveInteger where

import Lvl
open import Syntax.Number
open import Data.Boolean.Stmt
open import Functional
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural
open import Type

data ℕ₊ : Type{Lvl.𝟎} where
 𝟏 : ℕ₊
 𝐒 : ℕ₊ → ℕ₊

ℕ₊-to-ℕ : ℕ₊ → ℕ
ℕ₊-to-ℕ (𝟏)    = ℕ.𝐒(ℕ.𝟎)
ℕ₊-to-ℕ (𝐒(n)) = ℕ.𝐒(ℕ₊-to-ℕ (n))

ℕ-to-ℕ₊ : (n : ℕ) → ⦃ _ : IsTrue(positive?(n)) ⦄ → ℕ₊
ℕ-to-ℕ₊ (ℕ.𝟎)         ⦃ ⦄
ℕ-to-ℕ₊ (ℕ.𝐒(𝟎))      ⦃ _ ⦄ = 𝟏
ℕ-to-ℕ₊ (ℕ.𝐒(ℕ.𝐒(x))) ⦃ p ⦄ = 𝐒(ℕ-to-ℕ₊ (ℕ.𝐒(x)) ⦃ p ⦄)

instance
  ℕ₊-numeral : Numeral(ℕ₊)
  Numeral.restriction-ℓ (ℕ₊-numeral) = Lvl.𝟎
  Numeral.restriction   (ℕ₊-numeral) (n) = IsTrue(positive?(n))
  num ⦃ ℕ₊-numeral ⦄ (n) ⦃ proof ⦄ = ℕ-to-ℕ₊ (n) ⦃ proof ⦄

𝐒-from-ℕ : ℕ → ℕ₊
𝐒-from-ℕ (𝟎)    = 𝟏
𝐒-from-ℕ (𝐒(n)) = 𝐒(𝐒-from-ℕ(n))

𝐏-to-ℕ : ℕ₊ → ℕ
𝐏-to-ℕ (𝟏)    = 𝟎
𝐏-to-ℕ (𝐒(n)) = 𝐒(𝐏-to-ℕ(n))
