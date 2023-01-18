import      Lvl
open import Type

module Formalization.RegularExpression {ℓ} (Σ : Type{ℓ}) where

open import Data.List as List using (List)
open import Numeral.Natural

-- TODO: https://en.wikipedia.org/wiki/Kleene_algebra

data RegExp : Type{ℓ} where
  ∅ : RegExp     -- Empty language (Consisting of no words).
  ε : RegExp     -- Empty word language (Consisting of a single empty word).
  • : Σ → RegExp -- Singleton language (Consisting of a single one letter word).
  _·_ : RegExp → RegExp → RegExp -- Concatenation language (Consisting of the words concatenated pairwise).
  _+_  : RegExp → RegExp → RegExp -- Union language (Consisting of the words in both languages).
  _*   : RegExp → RegExp          -- Infinite concatenations language (Consisting of the words concatenated with themselves any number of times).

-- Non-empty infinite concatenations language.
_⁺ : RegExp → RegExp
e ⁺ = e · (e *)

-- Optional expression language
_?? : RegExp → RegExp
e ?? = ε + e

-- Finitely repeated expression language
exactly : ℕ → RegExp → RegExp
exactly 𝟎      e = ε
exactly (𝐒(n)) e = e · (exactly n e)

-- Minimum repetitions of an expression language
atLeast : ℕ → RegExp → RegExp
atLeast 𝟎      e = e *
atLeast (𝐒(n)) e = e · (atLeast n e)

-- Maximum repetitions of an expression language
atMost : ℕ → RegExp → RegExp
atMost 𝟎      e = ε
atMost (𝐒(n)) e = ε + (e · (atMost n e))
