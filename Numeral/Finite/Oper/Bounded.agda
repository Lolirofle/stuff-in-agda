-- Operators in which underflow and overflow is handled by stopping at the boundary.
-- An operation that tries to increase the value beyond the maximum stops at the maximum.
-- These operator's return type boundaries are therefore able to be arbitrary.
-- Formally for an unary operator (F: ℕ → ℕ), translated into an operator (f: 𝕟(b₁) → 𝕟(b₂)):
--   ∀(n: 𝕟(b₁)). max(𝐏(b₂)) (F(toℕ(n))) = toℕ(f(n))
--   toℕ preserves the operation that f and (max(𝐏(b₂)) ∘ F) represent.
module Numeral.Finite.Oper.Bounded where

open import Numeral.Finite as 𝕟 using (𝕟)
open import Numeral.Natural as ℕ using (ℕ)
import      Numeral.Natural.Relation as ℕ

-- Examples:
--   fromℕ{3} 0 = 0
--   fromℕ{3} 1 = 1
--   fromℕ{3} 2 = 2
--   fromℕ{3} 3 = 2
--   fromℕ{3} 4 = 2
fromℕ : ∀{b} .⦃ pos : ℕ.Positive(b) ⦄ → ℕ → 𝕟(b)
fromℕ{ℕ.𝐒 ℕ.𝟎}    _        = 𝕟.𝟎 -- Bounding case
fromℕ{ℕ.𝐒(ℕ.𝐒 _)} ℕ.𝟎      = 𝕟.𝟎
fromℕ{ℕ.𝐒(ℕ.𝐒 _)} (ℕ.𝐒(x)) = 𝕟.𝐒(fromℕ x)

-- Examples:
--   rebound{4}{3} 0 = 0
--   rebound{4}{3} 1 = 1
--   rebound{4}{3} 2 = 2
--   rebound{4}{3} 3 = 2
rebound : ∀{b₁ b₂} .⦃ pos : ℕ.Positive(b₂) ⦄ → 𝕟(b₁) → 𝕟(b₂)
rebound{b₂ = ℕ.𝐒 ℕ.𝟎}    _        = 𝕟.𝟎 -- Bounding case
rebound{b₂ = ℕ.𝐒(ℕ.𝐒 _)} 𝕟.𝟎      = 𝕟.𝟎
rebound{b₂ = ℕ.𝐒(ℕ.𝐒 _)} (𝕟.𝐒(x)) = 𝕟.𝐒(rebound x)

-- Predecessor bounded at the minimum (0).
-- Examples:
--   (𝐏₀(5): 𝕟(8)) = (4: 𝕟(8))
--   (𝐏₀(0): 𝕟(8)) = (0: 𝕟(8))
𝐏 : ∀{b₁ b₂} .⦃ pos : ℕ.Positive(b₂) ⦄ → 𝕟(b₁) → 𝕟(b₂)
𝐏{b₂ = ℕ.𝐒 ℕ.𝟎}     _                 = 𝕟.𝟎 -- Bounding case (upper bound)
𝐏{b₂ = ℕ.𝐒(ℕ.𝐒 b₂)} 𝕟.𝟎               = 𝕟.𝟎 -- Bounding case (lower bound)
𝐏{b₂ = ℕ.𝐒(ℕ.𝐒 b₂)} (𝕟.𝐒(𝕟.𝟎))        = 𝕟.𝟎
𝐏{b₂ = ℕ.𝐒(ℕ.𝐒 b₂)} (𝕟.𝐒(n@(𝕟.𝐒(_)))) = 𝕟.𝐒(𝐏(n))

-- Successor bounded at the maximum.
-- Examples:
--   (𝐒₀(5): 𝕟(8)) = (6: 𝕟(8))
--   (𝐒₀(7): 𝕟(8)) = (7: 𝕟(8))
𝐒 : ∀{b₁ b₂} .⦃ pos : ℕ.Positive(b₂) ⦄ → 𝕟(b₁) → 𝕟(b₂)
𝐒{b₂ = ℕ.𝐒 ℕ.𝟎}     _       = 𝕟.𝟎 -- Bounding case
𝐒{b₂ = ℕ.𝐒(ℕ.𝐒 b₂)} 𝕟.𝟎     = 𝕟.𝐒(𝕟.𝟎)
𝐒{b₂ = ℕ.𝐒(ℕ.𝐒 b₂)} (𝕟.𝐒 n) = 𝕟.𝐒(𝐒 n)

_+_ : ∀{b₁ b₂ b₃} .⦃ pos : ℕ.Positive(b₃) ⦄ → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₃)
_+_ {b₃ = ℕ.𝐒 ℕ.𝟎}    _       _       = 𝕟.𝟎 -- Bounding case
_+_ {b₃ = ℕ.𝐒(ℕ.𝐒 _)} 𝕟.𝟎     𝕟.𝟎     = 𝕟.𝟎
_+_ {b₃ = ℕ.𝐒(ℕ.𝐒 _)} z@𝕟.𝟎   (𝕟.𝐒 b) = 𝕟.𝐒(z + b)
_+_ {b₃ = ℕ.𝐒(ℕ.𝐒 _)} (𝕟.𝐒 a) b       = 𝕟.𝐒(a + b)

_−_ : ∀{b₁ b₂ b₃} .⦃ pos : ℕ.Positive(b₃) ⦄ → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₃)
_−_ {b₃ = ℕ.𝐒 ℕ.𝟎}    _       _       = 𝕟.𝟎 -- Bounding case (upper bound)
_−_ {b₃ = ℕ.𝐒(ℕ.𝐒 _)} 𝕟.𝟎     𝕟.𝟎     = 𝕟.𝟎
_−_ {b₃ = ℕ.𝐒(ℕ.𝐒 _)} 𝕟.𝟎     (𝕟.𝐒 b) = 𝕟.𝟎 -- Bounding case (lower bound)
_−_ {b₃ = ℕ.𝐒(ℕ.𝐒 _)} (𝕟.𝐒 a) z@𝕟.𝟎   = 𝕟.𝐒(a + z)
_−_ {b₃ = ℕ.𝐒(ℕ.𝐒 _)} (𝕟.𝐒 a) (𝕟.𝐒 b) = a − b

_⋅_ : ∀{b₁ b₂ b₃} .⦃ pos : ℕ.Positive(b₃) ⦄ → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₃)
_⋅_ {b₃ = ℕ.𝐒 ℕ.𝟎}         _       _ = 𝕟.𝟎 -- Bounding case
_⋅_ {b₃ = ℕ.𝐒 (ℕ.𝐒 _)}     𝕟.𝟎     _ = 𝕟.𝟎
_⋅_ {b₃ = b₃@(ℕ.𝐒(ℕ.𝐒 _))} (𝕟.𝐒 a) b = b + (_⋅_ {b₃ = b₃} a b)

_𝄩_ : ∀{b₁ b₂ b₃} .⦃ pos : ℕ.Positive(b₃) ⦄ → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₃)
_𝄩_ {b₃ = ℕ.𝐒 ℕ.𝟎}      _       _       = 𝕟.𝟎 -- Bounding case
_𝄩_ {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} 𝕟.𝟎     𝕟.𝟎     = 𝕟.𝟎
_𝄩_ {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} z@𝕟.𝟎   (𝕟.𝐒 b) = 𝕟.𝐒(z 𝄩 b)
_𝄩_ {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} (𝕟.𝐒 a) z@𝕟.𝟎   = 𝕟.𝐒(a 𝄩 z)
_𝄩_ {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} (𝕟.𝐒 a) (𝕟.𝐒 b) = a 𝄩 b

min : ∀{b₁ b₂ b₃} .⦃ pos : ℕ.Positive(b₃) ⦄ → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₃)
min {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} (𝕟.𝐒 a) (𝕟.𝐒 b) = 𝕟.𝐒(min a b)
{-# CATCHALL #-}
min _ _ = 𝕟.minimum

max : ∀{b₁ b₂ b₃} .⦃ pos : ℕ.Positive(b₃) ⦄ → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₃)
max {b₃ = ℕ.𝐒 ℕ.𝟎}      _       _       = 𝕟.𝟎 -- Bounding case
max {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} 𝕟.𝟎     𝕟.𝟎     = 𝕟.𝟎
max {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} z@𝕟.𝟎   (𝕟.𝐒 b) = 𝕟.𝐒(max z b)
max {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} (𝕟.𝐒 a) z@𝕟.𝟎   = 𝕟.𝐒(max a z)
max {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} (𝕟.𝐒 a) (𝕟.𝐒 b) = 𝕟.𝐒(max a b)
