module Numeral.Finite where

import Lvl
open import Syntax.Number
open import Data.Boolean.Stmt
open import Functional
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural hiding (𝐏)
open import Type

-- A structure corresponding to a finite set of natural numbers (0,..,n−1).
-- Specifically an upper bounded set of natural numbers, and the boundary is strictly lesser than the parameter.
-- Positive integers including zero less than a specified integer (0≤_<n).
-- Or represented using a set: {(i∊ℕ). 0≤i<n}.
-- The structure works in the following way:
--   • 𝟎 can be constructed for any non-zero upper bound (n).
--   • 𝐒 can be constructed from only a smaller upper bounded 𝕟.
--       Example: A 𝕟 constructed through 𝐒{3} can only be the following:
--         0 ≡ 𝟎{3}
--         1 ≡ 𝐒{3} (𝟎{2})
--         2 ≡ 𝐒{3} (𝐒{2} (𝟎{1}))
--         3 ≡ 𝐒{3} (𝐒{2} (𝐒{1} (𝟎{0})))
--         because there is nothing that could fill the blank in (𝐒{3} (𝐒{2} (𝐒{1} (𝐒{0} (_))))).
--       The smallest upper bound that can be is 0 (from using ℕ and its definition).
--       This limits how many successors (𝐒) that can "fit".
data 𝕟 : ℕ → Type{Lvl.𝟎} where
  𝟎 : ∀{n} → 𝕟(ℕ.𝐒(n))        -- Zero
  𝐒 : ∀{n} → 𝕟(n) → 𝕟(ℕ.𝐒(n)) -- Successor function
{-# INJECTIVE 𝕟 #-}

𝕟₌ = 𝕟 ∘ 𝐒

bound : ∀{n} → 𝕟(n) → ℕ
bound{n} _ = n

minimum : ∀{n} → 𝕟(ℕ.𝐒(n))
minimum{_} = 𝟎

maximum : ∀{n} → 𝕟(ℕ.𝐒(n))
maximum{𝟎}    = 𝟎
maximum{𝐒(n)} = 𝐒(maximum{n})

𝕟-to-ℕ : ∀{n} → 𝕟(n) → ℕ
𝕟-to-ℕ {ℕ.𝟎}    ()
𝕟-to-ℕ {ℕ.𝐒(_)} (𝟎)    = ℕ.𝟎
𝕟-to-ℕ {ℕ.𝐒(_)} (𝐒(n)) = ℕ.𝐒(𝕟-to-ℕ (n))

ℕ-to-𝕟 : (x : ℕ) → ∀{n} → . ⦃ _ : IsTrue(x <? n) ⦄ → 𝕟(n)
ℕ-to-𝕟 (ℕ.𝟎)    {ℕ.𝟎}    ⦃ ⦄
ℕ-to-𝕟 (ℕ.𝐒(x)) {ℕ.𝟎}    ⦃ ⦄
ℕ-to-𝕟 (ℕ.𝟎)    {ℕ.𝐒(_)} ⦃ _ ⦄ = 𝟎
ℕ-to-𝕟 (ℕ.𝐒(x)) {ℕ.𝐒(n)} ⦃ p ⦄ = 𝐒(ℕ-to-𝕟 (x) {n} ⦃ p ⦄)

instance
  𝕟-from-ℕ : ∀{N} → Numeral(𝕟(N)) (n ↦ IsTrue(n <? N))
  num ⦃ 𝕟-from-ℕ {N} ⦄ n = ℕ-to-𝕟 n {N}
