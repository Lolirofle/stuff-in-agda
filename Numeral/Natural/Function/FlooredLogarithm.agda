module Numeral.Natural.Function.FlooredLogarithm where

open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Numeral.Natural
open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Structure.Relator.Ordering
open        Structure.Relator.Ordering.Strict.Properties

open import Functional
open import Lang.Inspect
open import Relator.Equals.Proofs.Equiv

-- The floored logarithm function (integer part).
-- Example using log 5 1024 (The logarithm of 1024 with base 5):
--   Actual value: log 5 1024 ≈ 4.3067656
--   By repeating the division algorithm until 0 or 1:
--     1024  = 204⋅5 + 4
--     204   = 40 ⋅5 + 4
--     40    = 8  ⋅5 + 0
--     8     = 1  ⋅5 + 3
--   1024 = (((1⋅5 + 3)⋅5 + 0)⋅5 + 4)⋅5 + 4
--        = (((1⋅5⋅5⋅5⋅5 + 3⋅5⋅5⋅5) + 0⋅5⋅5) + 4⋅5) + 4
--        = 5⋅5⋅5⋅5 + (3⋅5⋅5⋅5 + 0⋅5⋅5 + 4⋅5 + 4)
--   Let n = 5⋅5⋅5⋅5 = 5⁴
--       r = 3⋅5⋅5⋅5 + 0⋅5⋅5 + 4⋅5 + 4 = 3⋅5³ + 0⋅5² + 4⋅5¹ + 4⋅5⁰
--   Then 1024 = n + r
--   log 5 1024 = log 5 (n + r)
--              = (log 5 n) + (log 5 (1 + (r / n)))
--              = 4 + (log 5 (1 + (r / n)))
--   Note that (r < n) because r is the remainders from repeated division.
-- Example using log 10 1024 (The logarithm of 1024 with base 10):
--   Actual value: log 10 1024 ≈ 3.0103000
--   By repeating the division algorithm until 0 or 1:
--     1024  = 102⋅10 + 4
--     102   = 10 ⋅10 + 2
--     10    = 8  ⋅10 + 0
--     1     = 0  ⋅10 + 1 (This step is only for the ceiled variant)
--   1024 = (((0⋅10 + 1)⋅10 + 0)⋅10 + 2)⋅10 + 4
-- Haskell implementation of the example:
--   flooredRepeatedDiv a b = let (d,m) = (div a b , mod a b) in (d,m) : (if d >= b then flooredRepeatedDiv d b else [])
--   flooredLogInt b n = length(flooredRepeatedDiv n b)
--   flooredLogRem b n = foldr(\x y -> x + b*y) 0 (map snd (flooredRepeatedDiv n b))
--   flooredLogInt2 b n = if n >= b then succ(flooredLogInt2 b (div n b)) else 0
--   ceiledRepeatedDiv a b = let (d,m) = (div a b , mod a b) in (d,m) : (if d > 0 then ceiledRepeatedDiv d b else [])
--   baseDigits n b = map snd (ceiledRepeatedDiv n b)
⌊log⌋ : (b : ℕ) → ⦃ _ : IsTrue(b ≥? 2) ⦄ → (n : ℕ) → ⦃ _ : IsTrue(n ≥? 1) ⦄ → ℕ
⌊log⌋ b@(𝐒(𝐒 _)) n = ℕ-strong-recursion(const ℕ) f(n) where
  f : (n : ℕ) → ((i : ℕ) → (i < n) → ℕ) → ℕ
  f n       prev with (n ≥? b) | inspect (_≥? b) n
  f n       prev | 𝐹 | intro _ = 𝟎
  f n@(𝐒 _) prev | 𝑇 | intro _ = 𝐒(prev(n ⌊/⌋ b) ([⌊/⌋]-ltₗ {b = b}))

-- The ceiled logarithm function.
⌈log⌉Rec : (b : ℕ) → ⦃ _ : IsTrue(b ≥? 2) ⦄ → (n : ℕ) → ((i : ℕ) → (i < n) → ℕ) → ℕ
⌈log⌉Rec _          𝟎       prev = 𝟎
⌈log⌉Rec b@(𝐒(𝐒 _)) n@(𝐒 _) prev = 𝐒(prev(n ⌊/⌋ b) ([⌊/⌋]-ltₗ {b = b}))
⌈log⌉ : (b : ℕ) → ⦃ _ : IsTrue(b ≥? 2) ⦄ → (n : ℕ) → ⦃ _ : IsTrue(n ≥? 1) ⦄ → ℕ
⌈log⌉ b n = ℕ-strong-recursion(const ℕ) (⌈log⌉Rec b) n

open import Data.List
open import Numeral.Natural.Oper.Modulo

-- The remainders of the ceiled logarithm function.
⌈log⌉Remainders : (b : ℕ) → ⦃ _ : IsTrue(b ≥? 2) ⦄ → (n : ℕ) → ⦃ _ : IsTrue(n ≥? 1) ⦄ → List(ℕ)
⌈log⌉Remainders b@(𝐒(𝐒 _)) n = ℕ-strong-recursion(const(List(ℕ))) f(n) where
  f : (n : ℕ) → ((i : ℕ) → (i < n) → List(ℕ)) → List(ℕ)
  f 𝟎       prev = ∅
  f n@(𝐒 _) prev = (n mod b) ⊰ (prev(n ⌊/⌋ b) ([⌊/⌋]-ltₗ {b = b}))

{-
⌈log⌉-intro : ∀{ℓ} → (P : ℕ → ℕ → Type{ℓ})
            → ((b : ℕ) ⦃ _ : IsTrue(b ≥? 2) ⦄
            → P(𝟎)(𝟎)
            → (∀{x y} → P((x ⌊/⌋ b) ⦃ {!!} ⦄)(𝐏 y) → P(x)(y))
            → (n : ℕ) ⦃ _ : IsTrue(n ≥? 1) ⦄ → P(n)(⌈log⌉ b n))
⌈log⌉-intro P b@(𝐒(𝐒 _)) base step n = ℕ-strong-recursion-intro{T = const ℕ}{rec = ⌈log⌉Rec b}{P = P} p n where
  p : (y : ℕ) → ((x : ℕ) → (x < y) → P x (ℕ-strong-recursion (const ℕ) (⌈log⌉Rec b) x)) → P y (ℕ-strong-recursion (const ℕ) (⌈log⌉Rec b) y)
  p 𝟎       _    = base
  p y@(𝐒 _) prev = step{y}{⌈log⌉ b y} {!prev (y ⌊/⌋ b) ?!} --  step {!prev y ?!}
  -- step (prev(y ⌊/⌋ b) ([⌊/⌋]-ltₗ {b = b}))
-}
