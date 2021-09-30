{-# OPTIONS --cubical #-}

module Miscellaneous.LimNatural2 where

open import Data.Option as Option using (Option ; None ; Some)
import      Data.Option.Functions as Option
open import Functional
import      Lvl
open import Numeral.Natural as ℕ using (ℕ)
import      Numeral.Natural.Oper as ℕ
open import Type

-- TODO: Do this with ℚ₊

ℕ∞ = Option(ℕ)
pattern 𝟎 = Some ℕ.𝟎
pattern 𝟏 = Some ℕ.𝟏
pattern ∞ = None

𝐒  = Option.map ℕ.𝐒
𝐏₀ = Option.map ℕ.𝐏

_+_ = Option.and-combine(ℕ._+_)
infixl 10010 _+_

_⋅_ : ℕ∞ → ℕ∞ → ℕ∞
_⋅_ = Option.combine(ℕ._⋅_) $₂ \{ℕ.𝟎 → 𝟏 ; (ℕ.𝐒 _) → ∞}
infixl 10020 _⋅_

