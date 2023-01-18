module Numeral.Finite.Oper where

open import Data
open import Data.Boolean.Stmt
open import Data.Option
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
open import Numeral.Finite as 𝕟 using (𝕟 ; 𝕟₌ ; toℕ)
open import Numeral.Finite.Bound
import      Numeral.Finite.Relation.Order as 𝕟
open import Numeral.Natural as ℕ hiding (𝟎 ; 𝐒 ; 𝐏)
import      Numeral.Natural.Function as ℕ
open import Numeral.Natural.Function.Proofs
import      Numeral.Natural.Oper as ℕ
import      Numeral.Natural.Oper.Comparisons as ℕ
import      Numeral.Natural.Relation as ℕ
open import Relator.Equals
open import Relator.Equals.Proofs
open import Syntax.Number

-- Operations where the boundary on the 𝕟-type reflect the operation in ℕ almost exactly.
-- More specifically, the boundary should grow as much as the function grows (the values above the maximum value should never be reached semantically).
-- Formally for an unary operator F in ℕ, translated into an operator f in 𝕟(?):
--   • toℕ preserves the operation that f and F represent:
--     • F(𝟎) = toℕ(f(𝟎))
--     • ∀(N: ℕ)∀(n: 𝕟(N)). F(𝐒(toℕ(n))) = toℕ(f(n))
--   • The boundary of the range of f should be a function (B: ℕ → ℕ) which grows at least as quick as F:
--     • f: ∀{N} → 𝕟(N) → 𝕟(B(N))
--     • ∀(n : 𝕟(N)). B(N) > F(n)
--     • and preferably: B(N) = 𝐒(max(⊶ F))
module Exact where
  -- Predecessor function bounded at the minimum (0) for both the value and the bound.
  -- Example: (𝐏₀(5): 𝕟(8)) = (4: 𝕟(7))
  𝐏₀ : ∀{n} ⦃ pos : ℕ.Positive(ℕ.𝐏(n)) ⦄ → 𝕟(n) → 𝕟(ℕ.𝐏(n))
  𝐏₀(𝕟.𝟎)    = 𝕟.minimum
  𝐏₀(𝕟.𝐒(n)) = n

  -- Addition function for both the value and the bound.
  -- Example: (5: 𝕟₌(8)) + (4: 𝕟₌(6)) = ((5+4): 𝕟₌(8+6)) = (9: 𝕟₌(14))
  _+₌_ : ∀{b₁ b₂} → 𝕟₌(b₁) → 𝕟₌(b₂) → 𝕟₌(b₁ ℕ.+ b₂)
  _+₌_ {_}    {_}     𝕟.𝟎      𝕟.𝟎      = 𝕟.𝟎
  _+₌_ {b₁}   {ℕ.𝐒 _} 𝕟.𝟎      (𝕟.𝐒(b)) = 𝕟.𝐒(𝕟.𝟎{b₁} +₌ b)
  _+₌_ {ℕ.𝐒 _}{_}     (𝕟.𝐒(a)) b        = 𝕟.𝐒(a +₌ b)

  _+_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₁ ℕ.+ b₂)
  _+_ {ℕ.𝐒 b₁} {ℕ.𝐒 b₂} a b = bound-𝐒(a +₌ b)

  -- Distance between two numbers.
  -- Examples:
  --   (3: 𝕟(8)) 𝄩 (5: 𝕟(6)) = ((3𝄩5): 𝕟(max 8 6)) = (2: 𝕟(8))
  --   (5: 𝕟(8)) 𝄩 (3: 𝕟(6)) = ((5𝄩3): 𝕟(max 8 6)) = (2: 𝕟(8))
  --   (7: 𝕟(8)) 𝄩 (0: 𝕟(6)) = ((7𝄩0): 𝕟(max 8 6)) = (7: 𝕟(8))
  _𝄩_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(ℕ.max b₁ b₂)
  _𝄩_ {ℕ.𝐒 b₁}       {ℕ.𝐒 b₂}       𝕟.𝟎     𝕟.𝟎     = 𝕟.𝟎
  _𝄩_ {ℕ.𝐒 ℕ.𝟎}      {ℕ.𝐒 b₂}       𝕟.𝟎     (𝕟.𝐒 b) = 𝕟.𝐒 b
  _𝄩_ {ℕ.𝐒 (ℕ.𝐒 b₁)} {ℕ.𝐒 b₂}       𝕟.𝟎     (𝕟.𝐒 b) = 𝕟.𝐒(𝕟.𝟎 𝄩 b)
  _𝄩_ {ℕ.𝐒 b₁}       {ℕ.𝐒 b₂}       (𝕟.𝐒 a) (𝕟.𝐒 b) = bound-𝐒(a 𝄩 b)
  _𝄩_ {ℕ.𝐒 b₁}       {ℕ.𝐒 ℕ.𝟎}      (𝕟.𝐒 a) 𝕟.𝟎     = 𝕟.𝐒 a
  _𝄩_ {ℕ.𝐒 b₁}       {ℕ.𝐒 (ℕ.𝐒 b₂)} (𝕟.𝐒 a) 𝕟.𝟎     = 𝕟.𝐒(a 𝄩 𝕟.𝟎)

  _⋅_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₁ ℕ.⋅ b₂)
  _⋅_ {ℕ.𝐒 b₁} {ℕ.𝐒 b₂} a 𝕟.𝟎     = 𝕟.𝟎
  _⋅_ {ℕ.𝐒 b₁} {ℕ.𝐒 b₂} a (𝕟.𝐒 b) = a + (a ⋅ b)

  _⋅₌_ : ∀{b₁ b₂} → 𝕟₌(b₁) → 𝕟₌(b₂) → 𝕟₌(b₁ ℕ.⋅ b₂)
  _⋅₌_              a 𝕟.𝟎     = 𝕟.𝟎
  _⋅₌_ {b₂ = ℕ.𝐒 _} a (𝕟.𝐒 b) = a +₌ (a ⋅₌ b)

module Optional where
  import Data.Option.Functions as Option

  𝐏 : ∀{n} → 𝕟(ℕ.𝐒(n)) → Option(𝕟(n))
  𝐏(𝕟.𝟎)    = None
  𝐏(𝕟.𝐒(x)) = Some(x)

  minimum : ∀{n} → Option(𝕟(n))
  minimum{ℕ.𝟎}    = None
  minimum{ℕ.𝐒(_)} = Some 𝕟.minimum

  maximum : ∀{n} → Option(𝕟(n))
  maximum{ℕ.𝟎}    = None
  maximum{ℕ.𝐒(n)} = Some 𝕟.maximum

  restrict : ℕ → (r : ℕ) → Option(𝕟(r))
  restrict(ℕ.𝟎)    _        = minimum
  restrict(ℕ.𝐒(_)) ℕ.𝟎      = None
  restrict(ℕ.𝐒(n)) (ℕ.𝐒(r)) = Option.map 𝕟.𝐒(restrict n r)

  -- `shift c` is the sequence where `c` is removed and mapped to `None`. All numbers greater than `c` are shifted towards zero.
  -- Note: A generalised 𝐏 in the following sense: shift 𝟎 ⊜ 𝐏
  -- Alternative definition by cases:
  --   (x < min(c,n)) → (shift𝐏{n} c x = Some(x))
  --   (x = min(c,n)) → (shift𝐏{n} c x = None)
  --   (x > min(c,n)) → (shift𝐏{n} c x = Some(𝐏(x)))
  -- Example in ℕ (using function tables):
  --   shift𝐏 0 = (0 ↦ None   ; 1 ↦ Some 0 ; 2 ↦ Some 1 ; 3 ↦ Some 2 ; 4 ↦ Some 3 ; …)
  --   shift𝐏 1 = (0 ↦ Some 0 ; 1 ↦ None   ; 2 ↦ Some 1 ; 3 ↦ Some 2 ; 4 ↦ Some 3 ; …)
  --   shift𝐏 2 = (0 ↦ Some 0 ; 1 ↦ Some 1 ; 2 ↦ None   ; 3 ↦ Some 2 ; 4 ↦ Some 3 ; …)
  --   shift𝐏 3 = (0 ↦ Some 0 ; 1 ↦ Some 1 ; 2 ↦ Some 2 ; 3 ↦ None   ; 4 ↦ Some 3 ; …)
  -- Example in ℕ (using function tables, skipping None cases and truncating Some):
  --   shift𝐏 0 = (        1 ↦ 0 ; 2 ↦ 1 ; 3 ↦ 2 ; 4 ↦ 3 ; …)
  --   shift𝐏 1 = (0 ↦ 0 ;         2 ↦ 1 ; 3 ↦ 2 ; 4 ↦ 3 ; …)
  --   shift𝐏 2 = (0 ↦ 0 ; 1 ↦ 1 ;         3 ↦ 2 ; 4 ↦ 3 ; …)
  --   shift𝐏 3 = (0 ↦ 0 ; 1 ↦ 1 ; 2 ↦ 2 ;         4 ↦ 3 ; …)
  --   shift𝐏 4 = (0 ↦ 0 ; 1 ↦ 1 ; 2 ↦ 2 ; 3 ↦ 3 ;         …)
  --   shift𝐏 5 = (0 ↦ 0 ; 1 ↦ 1 ; 2 ↦ 2 ; 3 ↦ 3 ; 4 ↦ 4 ; …)
  shift𝐏 : ∀{n m} → 𝕟(m) → 𝕟(ℕ.𝐒(n)) → Option(𝕟(n))
  shift𝐏 {ℕ.𝟎}   _        _        = None
  shift𝐏 {ℕ.𝐒 _} 𝕟.𝟎      𝕟.𝟎      = None
  shift𝐏 {ℕ.𝐒 _} (𝕟.𝐒(c)) 𝕟.𝟎      = Some(𝕟.𝟎)
  shift𝐏 {ℕ.𝐒 _} 𝕟.𝟎      (𝕟.𝐒(x)) = Some(x)
  shift𝐏 {ℕ.𝐒 _} (𝕟.𝐒(c)) (𝕟.𝐒(x)) = Option.map 𝕟.𝐒(shift𝐏 c x)

module Unclosed where
  _+ₙₗ_ : ∀{b₂} → (b₁ : ℕ) → 𝕟(b₂) → 𝕟(b₁ ℕ.+ b₂)
  ℕ.𝟎    +ₙₗ b = b
  ℕ.𝐒(a) +ₙₗ b = 𝕟.𝐒(a +ₙₗ b)

  _+ₙᵣ_ : ∀{b₁} → 𝕟(b₁) → (b₂ : ℕ) → 𝕟(b₁ ℕ.+ b₂)
  a +ₙᵣ ℕ.𝟎    = a
  a +ₙᵣ ℕ.𝐒(b) = 𝕟.𝐒(a +ₙᵣ b)

-- (shift𝐏ByRepeat c) is a mapping that shifts all numbers greater than c downwards.
-- It is similar to the identity mapping but skips 𝐒(c) and instead repeats c.
-- It is more similar to 𝐏 but instead of shifting all numbers down truncating at 0, it only shifts numbers greater than c and truncates at c.
-- Alternative definition by cases:
--   (x ≤ c) → (shift𝐏ByRepeat c x = id(x))
--   (x > c) → (shift𝐏ByRepeat c x = 𝐏(x))
-- Examples (Table of n = 4):
--   shift𝐏ByRepeat{4} 0 0 = 0
--   shift𝐏ByRepeat{4} 0 1 = 0
--   shift𝐏ByRepeat{4} 0 2 = 1
--   shift𝐏ByRepeat{4} 0 3 = 2
--   shift𝐏ByRepeat{4} 0 4 = 3
--
--   shift𝐏ByRepeat{4} 1 0 = 0
--   shift𝐏ByRepeat{4} 1 1 = 1
--   shift𝐏ByRepeat{4} 1 2 = 1
--   shift𝐏ByRepeat{4} 1 3 = 2
--   shift𝐏ByRepeat{4} 1 4 = 3
--
--   shift𝐏ByRepeat{4} 2 0 = 0
--   shift𝐏ByRepeat{4} 2 1 = 1
--   shift𝐏ByRepeat{4} 2 2 = 2
--   shift𝐏ByRepeat{4} 2 3 = 2
--   shift𝐏ByRepeat{4} 2 4 = 3
--
--   shift𝐏ByRepeat{4} 3 0 = 0
--   shift𝐏ByRepeat{4} 3 1 = 1
--   shift𝐏ByRepeat{4} 3 2 = 2
--   shift𝐏ByRepeat{4} 3 3 = 3
--   shift𝐏ByRepeat{4} 3 4 = 3
shift𝐏ByRepeat : ∀{n} → 𝕟(n) → (𝕟(ℕ.𝐒(n)) → 𝕟(n))
shift𝐏ByRepeat c        𝕟.𝟎      = 𝕟.minimum ⦃ 𝕟.𝕟-to-positive-bound c ⦄
shift𝐏ByRepeat 𝕟.𝟎      (𝕟.𝐒(x)) = x
shift𝐏ByRepeat (𝕟.𝐒(c)) (𝕟.𝐒(x)) = 𝕟.𝐒(shift𝐏ByRepeat c x)

-- (shift𝐏BySkip c) is a mapping that shifts all numbers greater than c downwards.
-- It is functionally equivalent to shift𝐏ByRepeat, but instead skips the case of (c = x).
shift𝐏BySkip :  ∀{n} → (c : 𝕟(ℕ.𝐒(n))) → (x : 𝕟(ℕ.𝐒(n))) → .⦃ c 𝕟.≢ x ⦄ → 𝕟(n)
shift𝐏BySkip {ℕ.𝟎}   (𝕟.𝐒(c)) 𝕟.𝟎      = c
shift𝐏BySkip {ℕ.𝐒 _} _        𝕟.𝟎      = 𝕟.𝟎
shift𝐏BySkip {ℕ.𝐒 _} 𝕟.𝟎      (𝕟.𝐒(x)) = x
shift𝐏BySkip {ℕ.𝐒 _} (𝕟.𝐒(c)) (𝕟.𝐒(x)) = 𝕟.𝐒(shift𝐏BySkip c x)

-- Note: shift𝐏ByRepeatRestrict is equal to shift𝐏ByRepeat. The difference is the bounding case, similar to the ones found in Bounded.*.
shift𝐏ByRepeatRestrict : ∀{m n} ⦃ pos : ℕ.Positive(n) ⦄ → 𝕟(m) → (𝕟(ℕ.𝐒(n)) → 𝕟(n))
shift𝐏ByRepeatRestrict {_}{ℕ.𝐒 ℕ.𝟎}    _        _        = 𝕟.𝟎 -- Bounding case
shift𝐏ByRepeatRestrict {_}{ℕ.𝐒(ℕ.𝐒 _)} _        𝕟.𝟎      = 𝕟.𝟎
shift𝐏ByRepeatRestrict {_}{ℕ.𝐒(ℕ.𝐒 _)} 𝕟.𝟎      (𝕟.𝐒(x)) = x
shift𝐏ByRepeatRestrict {_}{ℕ.𝐒(ℕ.𝐒 _)} (𝕟.𝐒(c)) (𝕟.𝐒(x)) = 𝕟.𝐒(shift𝐏ByRepeatRestrict c x)

-- Alternative definition by cases:
--   (x < c) → (shift𝐒 c x = id(x))
--   (x ≥ c) → (shift𝐒 c x = 𝐒(x))
-- Examples (Table of n = 4):
--   shift𝐒{4} 0 0 = 1
--   shift𝐒{4} 0 1 = 2
--   shift𝐒{4} 0 2 = 3
--   shift𝐒{4} 0 3 = 4
--
--   shift𝐒{4} 1 0 = 0
--   shift𝐒{4} 1 1 = 2
--   shift𝐒{4} 1 2 = 3
--   shift𝐒{4} 1 3 = 4
--
--   shift𝐒{4} 2 0 = 0
--   shift𝐒{4} 2 1 = 1
--   shift𝐒{4} 2 2 = 3
--   shift𝐒{4} 2 3 = 4
--
--   shift𝐒{4} 3 0 = 0
--   shift𝐒{4} 3 1 = 1
--   shift𝐒{4} 3 2 = 2
--   shift𝐒{4} 3 3 = 4
--
--   shift𝐒{4} 4 0 = 0
--   shift𝐒{4} 4 1 = 1
--   shift𝐒{4} 4 2 = 2
--   shift𝐒{4} 4 3 = 3
shift𝐒 : ∀{n m} → 𝕟(m) → 𝕟(n) → 𝕟(ℕ.𝐒(n))
shift𝐒 𝕟.𝟎      x        = 𝕟.𝐒(x)
shift𝐒 (𝕟.𝐒(c)) 𝕟.𝟎      = 𝕟.𝟎
shift𝐒 (𝕟.𝐒(c)) (𝕟.𝐒(x)) = 𝕟.𝐒(shift𝐒 c x)
