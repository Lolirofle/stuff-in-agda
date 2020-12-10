module Data.Boolean.Numeral where

open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
import      Lvl
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Syntax.Number
open import Type

Bool-to-ℕ : Bool → ℕ
Bool-to-ℕ 𝐹 = 0
Bool-to-ℕ 𝑇 = 1

ℕ-to-Bool : (n : ℕ) → . ⦃ _ : IsTrue(n <? 2) ⦄ → Bool
ℕ-to-Bool 0 = 𝐹
ℕ-to-Bool 1 = 𝑇

instance
  Bool-from-ℕ : Numeral(Bool)
  Numeral.restriction-ℓ Bool-from-ℕ     = Lvl.𝟎
  Numeral.restriction   Bool-from-ℕ   n = IsTrue(n <? 2)
  num                 ⦃ Bool-from-ℕ ⦄ n = ℕ-to-Bool n
