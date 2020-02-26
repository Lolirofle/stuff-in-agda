module Numeral.Natural.Combinatorics where

open import Numeral.Natural
open import Numeral.Natural.Oper

-- Counting combinations.
-- `𝑐𝐶 n k` is the number of ways one can pick `k` number of distinct objects from a set of `n` number of distinct objects.
-- Equivalently, it is the number of `k`-sized subsets of an `n`-sized set.
-- Also called: Binomial coefficients
-- Formulated using sets:
--   𝐶: Set → ℕ → Set
--   𝐶 S k = {(K∊℘(S)). #K = k}
--   𝑐𝐶(n) = #𝐶(𝕟(n))
𝑐𝐶 : ℕ → ℕ → ℕ
𝑐𝐶 _     𝟎     = 𝐒 𝟎
𝑐𝐶 𝟎     (𝐒 k) = 𝟎
𝑐𝐶 (𝐒 n) (𝐒 k) = 𝑐𝐶 n k + 𝑐𝐶 n (𝐒 k)

-- Counting partial permutations.
-- `𝑐𝑃 n k` is the number of arrangements for a list of `n` number of distinct objects into `k` number of objects.
-- Equivalently, it is the number of injective functions (function equality by the standard function extensionality) of type `𝕟(k) → 𝕟(n)`.
-- Also called: Falling factorial
-- Formulated using sets:
--   𝑃: Set → ℕ → Set
--   𝑃 S k = {(π: 𝕟(k) → S). Injective(π)}
--   𝑐𝑃(n) = #𝑃(𝕟(n))
𝑐𝑃 : ℕ → ℕ → ℕ
𝑐𝑃 _     𝟎     = 𝐒 𝟎
𝑐𝑃 𝟎     (𝐒 k) = 𝟎
𝑐𝑃 (𝐒 n) (𝐒 k) = 𝑐𝑃 n k ⋅ (𝐒 n)

-- Counting derangements.
-- `𝑐𝐷(n)` is the number of permutations of a list of `n` number of distinct objects such that in every permutation, no object is permuted with itself.
-- Formulated using sets:
--   𝐷: Set → Set
--   𝐷(S) = {(π∊𝑃(S)). ∀(s∊S). π(s) ≠ s}
--   𝑐𝐷(n) = #𝐷(𝕟(n))
𝑐𝐷 : ℕ → ℕ
𝑐𝐷(𝟎)      = 𝐒 𝟎
𝑐𝐷(𝐒 𝟎)    = 𝟎
𝑐𝐷(𝐒(𝐒 n)) = 𝐒(n) ⋅ (𝑐𝐷 (𝐒 n) + 𝑐𝐷 n)

-- Stirling numbers of the first kind.
stir₁ : ℕ → ℕ → ℕ
stir₁ 𝟎      𝟎      = 𝐒(𝟎)
stir₁ (𝐒(n)) 𝟎      = 𝟎
stir₁ 𝟎      (𝐒(k)) = 𝟎
stir₁ (𝐒(n)) (𝐒(k)) = (n ⋅ stir₁ n (𝐒(k))) + stir₁ n k

-- Stirling numbers of the second kind.
stir₂ : ℕ → ℕ → ℕ
stir₂ 𝟎      𝟎      = 𝐒(𝟎)
stir₂ (𝐒(n)) 𝟎      = 𝟎
stir₂ 𝟎      (𝐒(k)) = 𝟎
stir₂ (𝐒(n)) (𝐒(k)) = (𝐒(k) ⋅ stir₂ n (𝐒(k))) + stir₂ n k

-- Counting injective functions.
𝑐𝐼𝑛𝑗 : ℕ → ℕ → ℕ
𝑐𝐼𝑛𝑗 = 𝑐𝑃

-- Counting surjective functions.
𝑐𝑆𝑢𝑟𝑗 : ℕ → ℕ → ℕ
𝑐𝑆𝑢𝑟𝑗 a b = stir₂ a b ⋅ (b !)
