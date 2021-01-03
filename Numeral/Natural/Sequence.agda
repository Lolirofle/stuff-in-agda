module Numeral.Natural.Sequence where

import      Lvl
open import Data
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
import      Data.Tuple.Raise as Tuple
open import Functional
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.FlooredDivision
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable n : ℕ
private variable A : Type{ℓ}
private variable B : Type{ℓ}

-- Alternates between the two sides, starting with the left.
-- A countable bijection for the Either type.
-- Examples:
--   alternate₂(0) = Left(0)
--   alternate₂(2) = Left(1)
--   alternate₂(4) = Left(2)
--   alternate₂(6) = Left(3)

--   alternate₂(1) = Right(0)
--   alternate₂(3) = Right(1)
--   alternate₂(5) = Right(2)
--   alternate₂(7) = Right(3)
alternate₂ : ℕ → (ℕ ‖ ℕ)
alternate₂(0)       = Either.Left 0
alternate₂(1)       = Either.Right 0
alternate₂(𝐒(𝐒(n))) = Either.map 𝐒 𝐒 (alternate₂ n)

-- The inverse of `alternate₂`.
unalternate₂ : (ℕ ‖ ℕ) → ℕ
unalternate₂(Either.Left  n) = n ⋅ 2
unalternate₂(Either.Right n) = 𝐒(n ⋅ 2)

-- Maps two natural numbers to a single one without overlaps by following the inverse diagonals downwards.
-- A countable bijection for the tuple pairing type.
-- Alternative forms:
--   pairIndexing a b = a + (∑(𝕟(a + b)) (i ↦ 𝕟-to-ℕ(i)))
--   pairIndexing a b = a + ((a + b) * (a + b + 1) / 2)
-- Example:
--   Horizontal axis is `a` starting from 0.
--   Vertical axis is `b` starting from 0.
--   Cells are `pairIndexing a b`.
--    0, 1, 3, 6,10,15
--    2, 4, 7,11,16,..
--    5, 8,12,17,   ..
--    9,13,18,      ..
--   14,19,         ..
--   20,.. .. .. .. ..
-- Termination:
--   Decreases `a` until 0 while at the same time increases `b` (So `b` is at most `a`).
--   Then the arguments is swapped, but using the predecessor of `b`.
--   This means that `b` will eventually reach 0.
{-# TERMINATING #-}
pairIndexing : ℕ → ℕ → ℕ
pairIndexing 𝟎     𝟎     = 𝟎
pairIndexing (𝐒 a) 𝟎     = 𝐒(pairIndexing 𝟎 a)
{-# CATCHALL #-}
pairIndexing a     (𝐒 b) = 𝐒(pairIndexing (𝐒 a) b)

-- A sequence which fills a discrete two dimensional grid (a space bounded in two directions and infinite in the other two).
-- It is the inverse of an uncurried `pairIndexing`.
-- Example:
--   •-→-• ↗→• ↗→•
--     ↙ ↗ ↙ ↗ ↙
--   •→↗ • ↗ •   •
--     ↙ ↗ ↙
--   •→↗ •   •   •
diagonalFilling : ℕ → (ℕ ⨯ ℕ)
diagonalFilling 𝟎      = (𝟎 , 𝟎)
diagonalFilling (𝐒(n)) with diagonalFilling n
... | (𝟎    , b) = (𝐒(b) , 0)
... | (𝐒(a) , b) = (a , 𝐒(b))

tupleIndexing : (ℕ Tuple.^ n) → ℕ
tupleIndexing {𝟎}       <>      = 𝟎
tupleIndexing {𝐒(𝟎)}    x       = x
tupleIndexing {𝐒(𝐒(n))} (x , y) = pairIndexing x (tupleIndexing {𝐒(n)} y)

spaceFilling : ℕ → (ℕ Tuple.^ n)
spaceFilling {𝟎}          _ = <>
spaceFilling {𝐒(𝟎)}       i = i
spaceFilling {𝐒(𝐒(n))}    i = Tuple.mapRight (spaceFilling {𝐒(n)}) (diagonalFilling i)


-- Interleaves two sequences into one, alternating between the elements from each sequence.
interleave : (ℕ → A) → (ℕ → B) → (ℕ → (A ‖ B))
interleave af bf = Either.map af bf ∘ alternate₂

pair : (ℕ → A) → (ℕ → B) → (ℕ → (A ⨯ B))
pair af bf = Tuple.map af bf ∘ diagonalFilling
