module Numeral.FiniteStrict where

import Lvl
open import Syntax.Number
open import Data.Boolean.AsSet
open import Functional
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural hiding (𝐏)
import      Numeral.Natural.Relation.Order
open import Type

-- A structure corresponding to a finite set of natural numbers (0,..,n−1).
-- Specifically an upper bounded set of natural numbers, and the boundary is strictly lesser than the parameter.
-- Positive integers including zero less than a specified integer (0≤_<n).
-- This structure works in the following way:
--   • 𝟎 can always be constructed, for any upper bound (n).
--   • 𝐒 can only be constructed from a smaller upper bounded 𝕟.
--       Example: A 𝕟 constructed through 𝐒{3} can only be the following:
--         0 ≡ 𝟎{3}
--         1 ≡ 𝐒{3} (𝟎{2})
--         2 ≡ 𝐒{3} (𝐒{2} (𝟎{1}))
--         3 ≡ 𝐒{3} (𝐒{2} (𝐒{1} (𝟎{0})))
--         because there is nothing that could fill the blank in (𝐒{3} (𝐒{2} (𝐒{1} (𝐒{0} (_))))).
--       The smallest upper bound that can be is 0 (from using ℕ and its definition).
--       This limits how many successors (𝐒) that can "fit".
data 𝕟 : ℕ → Set where
  𝟎 : ∀{n} → 𝕟(ℕ.𝐒(n))                   -- Zero
  𝐒 : ∀{n} → 𝕟(ℕ.𝐒(n)) → 𝕟(ℕ.𝐒(ℕ.𝐒(n))) -- Successor function (TODO: The type could be 𝕟(n) → 𝕟(ℕ.𝐒(n))? 𝕟(𝟎) is impossible after all)
{-# INJECTIVE 𝕟 #-}

minimum : ∀{n} → 𝕟(ℕ.𝐒(n))
minimum{_} = 𝟎

maximum : ∀{n} → 𝕟(ℕ.𝐒(n))
maximum{𝟎}    = 𝟎
maximum{𝐒(n)} = 𝐒(maximum{n})

[𝕟]-to-[ℕ] : ∀{n} → 𝕟(ℕ.𝐒(n)) → ℕ
[𝕟]-to-[ℕ] (𝟎)    = ℕ.𝟎
[𝕟]-to-[ℕ] (𝐒(n)) = ℕ.𝐒([𝕟]-to-[ℕ] (n))

module _ {ℓ} where
  open Numeral.Natural.Relation.Order{ℓ}

  [ℕ]-to-[𝕟] : (x : ℕ) → ∀{n} → ⦃ _ : BoolIsTrue{ℓ}(x ≤? n) ⦄ → 𝕟(ℕ.𝐒(n))
  [ℕ]-to-[𝕟] (ℕ.𝟎)    {_}      ⦃ _ ⦄ = 𝟎
  [ℕ]-to-[𝕟] (ℕ.𝐒(_)) {ℕ.𝟎}    ⦃ ⦄
  [ℕ]-to-[𝕟] (ℕ.𝐒(x)) {ℕ.𝐒(n)} ⦃ p ⦄ = 𝐒([ℕ]-to-[𝕟] (x) {n} ⦃ p ⦄)

module _ where
  open Numeral.Natural.Relation.Order{Lvl.𝟎}

  instance
    𝕟-from-ℕ : ∀{N} → From-ℕsubset(𝕟(ℕ.𝐒(N)))
    From-ℕsubset.restriction ( 𝕟-from-ℕ {N} ) (n) = BoolIsTrue{Lvl.𝟎}(n ≤? N)
    from-ℕsubset ⦃ 𝕟-from-ℕ {N} ⦄ (n) ⦃ proof ⦄ = [ℕ]-to-[𝕟] (n) {N} ⦃ proof ⦄
