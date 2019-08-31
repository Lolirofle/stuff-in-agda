module Numeral.PositiveInteger where

import Lvl
open import Syntax.Number
open import Data.Boolean.Stmt
open import Functional
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural hiding (𝐏)
import      Numeral.Natural.Relation.Order
open import Type

data ℕ₊ : Set where
 𝟏 : ℕ₊
 𝐒 : ℕ₊ -> ℕ₊

[ℕ₊]-to-[ℕ] : ℕ₊ → ℕ
[ℕ₊]-to-[ℕ] (𝟏)    = ℕ.𝐒(ℕ.𝟎)
[ℕ₊]-to-[ℕ] (𝐒(n)) = ℕ.𝐒([ℕ₊]-to-[ℕ] (n))

module _ {ℓ} where
  open Numeral.Natural.Relation.Order{ℓ}

  [ℕ]-to-[ℕ₊] : (n : ℕ) → ⦃ _ : IsTrue{ℓ}(positive?(n)) ⦄ → ℕ₊
  [ℕ]-to-[ℕ₊] (ℕ.𝟎)         ⦃ ⦄
  [ℕ]-to-[ℕ₊] (ℕ.𝐒(𝟎))      ⦃ _ ⦄ = 𝟏
  [ℕ]-to-[ℕ₊] (ℕ.𝐒(ℕ.𝐒(x))) ⦃ p ⦄ = 𝐒([ℕ]-to-[ℕ₊] (ℕ.𝐒(x)) ⦃ p ⦄)

module _ where
  open Numeral.Natural.Relation.Order{Lvl.𝟎}

  instance
    ℕ₊-from-ℕ : Numeral(ℕ₊)
    Numeral.restriction ( ℕ₊-from-ℕ ) (n) = IsTrue{Lvl.𝟎}(positive?(n))
    num ⦃ ℕ₊-from-ℕ ⦄ (n) ⦃ proof ⦄ = [ℕ]-to-[ℕ₊] (n) ⦃ proof ⦄
