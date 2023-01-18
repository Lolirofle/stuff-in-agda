module Numeral.Finite where

import      Lvl
open import Data
open import Data.Boolean.Stmt
open import Data.Option
import      Data.Option.Functions as Option
open import Functional
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural as ℕ using (ℕ ; 𝟎 ; 𝐒)
import      Numeral.Natural.Relation as ℕ
open import Syntax.Number
open import Type.Dependent.Sigma.Implicit
open import Type

-- 𝕟(n) is a type representing a finite set of natural numbers (0,..,n−1).
-- In other words, it is an upper bounded set of natural numbers, and the boundary is strictly lesser than the parameter.
-- Positive integers including zero less than a specified integer: (0≤_<n).
-- Or using set notation: {(i∊ℕ). 0 ≤ i < n}.
-- The definition works in the following way:
-- • 𝟎 can be constructed for any non-zero upper bound (n).
-- • 𝐒 can be constructed from only a smaller upper bounded 𝕟.
--   Example: A 𝕟(4) constructed using 𝐒{3} can only be the following:
--     1 = 𝐒{3} (𝟎{2})
--     2 = 𝐒{3} (𝐒{2} (𝟎{1}))
--     3 = 𝐒{3} (𝐒{2} (𝐒{1} (𝟎{0})))
--     ? = 𝐒{3} (𝐒{2} (𝐒{1} (𝐒{0} (_) is not possible because 𝐒{0} accepts a 𝕟(0), which is an empty type.
--   This limits the number of successors (𝐒).
data 𝕟 : ℕ → Type{Lvl.𝟎} where
  𝟎 : ∀{n} → 𝕟(ℕ.𝐒(n))        -- Zero
  𝐒 : ∀{n} → 𝕟(n) → 𝕟(ℕ.𝐒(n)) -- Successor function
-- {-# INJECTIVE 𝕟 #-} -- Note: It is still injective without this pragma, but propositionally and not definitionally.

𝟏 : ∀{n} → 𝕟(ℕ.𝐒(ℕ.𝐒(n)))
𝟏 = 𝐒(𝟎)

-- 𝕟₌(n) is a type representing a finite set of natural numbers (0,..,n).
-- Or using set notation: {(i∊ℕ). 0 ≤ i ≤ n}.
𝕟₌ = 𝕟 ∘ 𝐒

-- 𝕟 but with an arbitrary type parameter.
-- Note: This is similar to ℕ.
𝕟* = ℰ 𝕟

-- 𝕟₌ but with an arbitrary type parameter.
-- Note: This is similar to ℕ.
𝕟₌* = ℰ 𝕟₌

-- The bound of a finite number.
bound : ∀{n} → 𝕟(n) → ℕ
bound{n} _ = n

-- The smallest finite number using a certain bound.
minimum : ∀{n} .⦃ pos : ℕ.Positive(n) ⦄ → 𝕟(n)
minimum{𝐒 _} = 𝟎

toℕ : ∀{n} → 𝕟(n) → ℕ
toℕ 𝟎      = ℕ.𝟎
toℕ (𝐒(n)) = ℕ.𝐒(toℕ (n))

fromℕ : (x : ℕ) → ∀{n} → .⦃ _ : IsTrue(x <? n) ⦄ → 𝕟(n)
fromℕ (ℕ.𝐒(x)) {ℕ.𝐒(n)} = 𝐒(fromℕ x {n})
fromℕ (ℕ.𝟎)             = minimum ⦃ p ⦄ where
  p : ∀{x n} → ⦃ IsTrue(x <? n) ⦄ → ℕ.Positive(n)
  p{n = 𝐒(n)} = <>

-- The greatest finite number using a certain bound.
maximum : ∀{n} .⦃ pos : ℕ.Positive(n) ⦄ → 𝕟(n)
maximum{n} = fromℕ (ℕ.𝐏(n)) {n} ⦃ p{n} ⦄ where
  p : ∀{n} → ⦃ pos : ℕ.Positive(n) ⦄ → IsTrue(ℕ.𝐏(n) <? n)
  p{𝐒(𝟎)}       = <>
  p{𝐒(n@(𝐒 _))} = p{n}

instance
  𝕟-numeral : ∀{N} → Numeral(𝕟(N)) (IsTrue ∘ (_<? N))
  num ⦃ 𝕟-numeral {N} ⦄ n = fromℕ n {N}

toℕ-bound : ∀{N}{n : 𝕟(N)} → IsTrue(toℕ n <? N)
toℕ-bound{n = 𝟎}   = <>
toℕ-bound{n = 𝐒 n} = toℕ-bound{n = n}

𝕟-to-positive-bound : ∀{N} → .(𝕟(N)) → ℕ.Positive(N)
𝕟-to-positive-bound {𝐒 N} _ = <>
