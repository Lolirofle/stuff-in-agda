module Numeral.Finite.Oper.Wrapping where

open import Data
open import Numeral.Finite as 𝕟 using (𝕟 ; 𝕟₌ ; toℕ)
open import Numeral.Finite.Bound
open import Numeral.Natural as ℕ hiding (𝟎 ; 𝐒 ; 𝐏)
import      Numeral.Natural.Relation as ℕ

-- Wrapping predecessor.
-- Example:
--   𝐏{4} 0 = 3
--   𝐏{4} 1 = 0
--   𝐏{4} 2 = 1
--   𝐏{4} 3 = 2
-- Alternative implementation (using _[−]_):
--   𝐏 = _[−] 𝕟.𝟏 {ℕ.𝟎}
𝐏 : ∀{b} → 𝕟(b) → 𝕟(b)
𝐏(𝕟.𝟎)    = 𝕟.maximum
𝐏(𝕟.𝐒(n)) = bound-𝐒(n)

-- Wrapping subtraction.
-- Essentially: _[−]_ {b₁}{b₂} a b = (a ℤ.− b) mod b₁
-- Alternative implementation (by inlining 𝐏):
--   _[−]_ {_}      {ℕ.𝐒 _}  a       𝕟.𝟎     = a
--   _[−]_ {ℕ.𝐒 b₁} {ℕ.𝐒 _}  𝕟.𝟎     (𝕟.𝐒 b) = 𝕟.maximum {ℕ.𝐒 b₁} [−] b
--   _[−]_ {ℕ.𝐒 b₁} {ℕ.𝐒 b₂} (𝕟.𝐒 a) (𝕟.𝐒 b) = _[−]_ {ℕ.𝐒 b₁}{b₂} (bound-𝐒 a) b
_[−]_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₁)
a [−] 𝕟.𝟎    = a
a [−] 𝕟.𝐒(b) = 𝐏(a) [−] b
infix  10010 _[−]_

-- (Flipping around the symmetric point)
-- Example:
--   flip{5} 0 = 4
--   flip{5} 1 = 3
--   flip{5} 2 = 2
--   flip{5} 3 = 1
--   flip{5} 4 = 0
flip : ∀{b} → 𝕟(b) → 𝕟(b)
flip n = 𝕟.maximum{𝕟.bound(n)} ⦃ 𝕟.𝕟-to-positive-bound n ⦄ [−] n

-- Wrapping subtraction of a ℕ and a 𝕟(_).
-- Examples:
--   5 [ₙ−] 0 = 0
--   5 [ₙ−] 1 = 4
--   5 [ₙ−] 2 = 3
--   5 [ₙ−] 3 = 2
--   5 [ₙ−] 4 = 1
--   5 [ₙ−] 5 = 0
--   5 [ₙ−] 6 = 4
--   5 [ₙ−] 7 = 3
_[ₙ−]_ : (b₁ : ℕ) .⦃ pos : ℕ.Positive(b₁) ⦄ → ∀{b₂} → 𝕟(b₂) → 𝕟(b₁)
a [ₙ−] b = 𝕟.minimum{a} [−] b
infix  10010 _[ₙ−]_

-- Wrapping negation.
-- Essentially: [−]_ {b} n = (ℤ.− n) mod b
-- Example:
--   [−]_ {5} 0 = 0
--   [−]_ {5} 1 = 4
--   [−]_ {5} 2 = 3
--   [−]_ {5} 3 = 2
--   [−]_ {5} 4 = 1
[−]_ : ∀{b} → 𝕟(b) → 𝕟(b)
[−] n = 𝕟.bound(n) [ₙ−] n where instance _ = 𝕟.𝕟-to-positive-bound n
infixl 10005 [−]_

-- Wrapping addition.
-- Essentially: _[−]_ {b₁}{b₂} a b = (a ℤ.+ b) mod b₁
_[+]_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₁)
a [+] b = a [−] (𝕟.bound(a) [ₙ−] b) where instance _ = 𝕟.𝕟-to-positive-bound a
infixl 10010 _[+]_

-- Wrapping successor.
-- Example:
--   𝐒{4} 0 = 1
--   𝐒{4} 1 = 2
--   𝐒{4} 2 = 3
--   𝐒{4} 3 = 0
𝐒 : ∀{b} → 𝕟(b) → 𝕟(b)
𝐒(n) = n [−] 𝕟.maximum{𝕟.bound(n)} ⦃ 𝕟.𝕟-to-positive-bound n ⦄

-- Modulo operator in 𝕟.
-- Example:
--   0 mod 3 = 0
--   1 mod 3 = 1
--   2 mod 3 = 2
--   3 mod 3 = 0
--   4 mod 3 = 1
--   5 mod 3 = 2
--   6 mod 3 = 0
--   7 mod 3 = 1
--   8 mod 3 = 2
--   9 mod 3 = 0
_mod_ : ∀{b} → 𝕟(b) → (m : ℕ) .⦃ pos : ℕ.Positive(m) ⦄ → 𝕟(m)
a mod m = 𝕟.minimum [+] a
infixl 10020 _mod_

-- Wrapping multiplication (repeated wrapping addition).
_[⋅]_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₁)
_[⋅]_ {ℕ.𝐒 _} a 𝕟.𝟎      = 𝕟.𝟎
_[⋅]_ {ℕ.𝐒 _} a (𝕟.𝐒(b)) = a [+] (a [⋅] b)
infixl 10020 _[⋅]_

-- Wrapping exponentiation (repeated wrapping multiplication).
_[^]_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₁)
_[^]_ {ℕ.𝐒(ℕ.𝟎)}   _ _        = 𝕟.𝟎
_[^]_ {ℕ.𝐒(ℕ.𝐒 _)} a 𝕟.𝟎      = 𝕟.𝐒(𝕟.𝟎)
_[^]_ {ℕ.𝐒(ℕ.𝐒 _)} a (𝕟.𝐒(b)) = a [⋅] (a [^] b)
infixl 10030 _[^]_

-- Like (_[−]_) but subtracting an ℕ instead.
_[−ₙ]_ : ∀{n} → 𝕟(n) → ℕ → 𝕟(n)
a [−ₙ] b = a [−] 𝕟.maximum{ℕ.𝐒(b)}
infix  10010 _[−ₙ]_

-- Like (_[+]_) but adding an ℕ instead.
_[+ₙ]_ : ∀{n} → 𝕟(n) → ℕ → 𝕟(n)
a [+ₙ] b = a [+] 𝕟.maximum{ℕ.𝐒(b)}
infix  10010 _[+ₙ]_

-- Alternative definition of the modulo operator (Alternative to Numeral.Natural.Oper.Modulo._mod_. The algorithm should be similar, but this uses the operators of 𝕟).
_modₙ_ : ℕ → (m : ℕ) ⦃ pos : ℕ.Positive(m) ⦄ → 𝕟(m)
a modₙ m = 𝕟.minimum [+ₙ] a
infix  10020 _modₙ_
