module Numeral.Finite.Oper where

open import Data
open import Data.Boolean.Stmt
open import Data.Option
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
open import Numeral.Finite as 𝕟 using (𝕟 ; 𝕟₌ ; 𝕟-to-ℕ)
open import Numeral.Finite.Bound
import      Numeral.Finite.Relation.Order as 𝕟
open import Numeral.Natural hiding (𝟎 ; 𝐒 ; 𝐏)
import      Numeral.Natural.Function as ℕ
open import Numeral.Natural.Function.Proofs
import      Numeral.Natural.Oper as ℕ
import      Numeral.Natural.Oper.Comparisons as ℕ
import      Numeral.Natural.Relation as ℕ
open import Relator.Equals
open import Relator.Equals.Proofs
open import Syntax.Number

module Exact where
  -- Predecessor bounded at the minimum (0) for both the value and the maximum.
  -- Example: (𝐏₀(5): 𝕟(8)) = (4: 𝕟(7))
  𝐏₀ : ∀{n} ⦃ pos : ℕ.Positive(n) ⦄ → 𝕟(ℕ.𝐒(n)) → 𝕟(n)
  𝐏₀ {ℕ.𝐒 _} (𝕟.𝟎)    = 𝕟.𝟎
  𝐏₀ {ℕ.𝐒 _} (𝕟.𝐒(n)) = n

  -- Addition for both the value and the maximum.
  -- Example: (5: 𝕟₌(8)) + (4: 𝕟₌(6)) = ((5+4): 𝕟₌(8+6)) = (9: 𝕟₌(14))
  _+_ : ∀{b₁ b₂} → 𝕟₌(b₁) → 𝕟₌(b₂) → 𝕟₌(b₁ ℕ.+ b₂)
  _+_ {_}    {_}     𝕟.𝟎      𝕟.𝟎      = 𝕟.𝟎
  _+_ {b₁}   {ℕ.𝐒 _} 𝕟.𝟎      (𝕟.𝐒(b)) = 𝕟.𝐒(𝕟.𝟎{b₁} + b)
  _+_ {ℕ.𝐒 _}{_}     (𝕟.𝐒(a)) b        = 𝕟.𝐒(a + b)

  _+₀_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₁ ℕ.+ b₂)
  _+₀_ {ℕ.𝐒 b₁} {ℕ.𝐒 b₂} a b = bound-𝐒(a + b)

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
  _⋅_ {ℕ.𝐒 b₁} {ℕ.𝐒 b₂} a (𝕟.𝐒 b) = a +₀ (a ⋅ b)

module Bounded where -- TODO: It may be possible to define many of the other operators by using these
  -- Predecessor bounded at the minimum (0).
  -- Examples:
  --   (𝐏₀(5): 𝕟(8)) = (4: 𝕟(8))
  --   (𝐏₀(0): 𝕟(8)) = (0: 𝕟(8))
  𝐏 : ∀{b₁ b₂} ⦃ pos : ℕ.Positive(b₂) ⦄ → 𝕟(b₁) → 𝕟(b₂)
  𝐏{b₂ = ℕ.𝐒 ℕ.𝟎}     _             = 𝕟.𝟎
  𝐏{b₂ = ℕ.𝐒(ℕ.𝐒 b₂)} 𝕟.𝟎           = 𝕟.𝟎
  𝐏{b₂ = ℕ.𝐒(ℕ.𝐒 b₂)} (𝕟.𝐒(𝕟.𝟎))    = 𝕟.𝟎
  𝐏{b₂ = ℕ.𝐒(ℕ.𝐒 b₂)} (𝕟.𝐒(𝕟.𝐒(n))) = 𝕟.𝐒(𝐏(𝕟.𝐒(n)))

  -- Successor bounded at the maximum.
  -- Examples:
  --   (𝐒₀(5): 𝕟(8)) = (6: 𝕟(8))
  --   (𝐒₀(7): 𝕟(8)) = (7: 𝕟(8))
  𝐒 : ∀{b₁ b₂} ⦃ pos : ℕ.Positive(b₂) ⦄ → 𝕟(b₁) → 𝕟(b₂)
  𝐒{b₂ = ℕ.𝐒 ℕ.𝟎}     _       = 𝕟.𝟎
  𝐒{b₂ = ℕ.𝐒(ℕ.𝐒 b₂)} 𝕟.𝟎     = 𝕟.𝐒(𝕟.𝟎)
  𝐒{b₂ = ℕ.𝐒(ℕ.𝐒 b₂)} (𝕟.𝐒 n) = 𝕟.𝐒(𝐒 n)

  _+_ : ∀{b₁ b₂ b₃} ⦃ pos : ℕ.Positive(b₃) ⦄ → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₃)
  _+_ {b₃ = ℕ.𝐒 ℕ.𝟎}      _       _       = 𝕟.𝟎
  _+_ {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} 𝕟.𝟎     𝕟.𝟎     = 𝕟.𝟎
  _+_ {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} z@𝕟.𝟎   (𝕟.𝐒 b) = 𝕟.𝐒(z + b)
  _+_ {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} (𝕟.𝐒 a) b       = 𝕟.𝐒(a + b)

  _⋅_ : ∀{b₁ b₂ b₃} ⦃ pos : ℕ.Positive(b₃) ⦄ → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₃)
  _⋅_ {b₃ = ℕ.𝐒 ℕ.𝟎}      _       _ = 𝕟.𝟎
  _⋅_ {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} 𝕟.𝟎     _ = 𝕟.𝟎
  _⋅_ {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} (𝕟.𝐒 a) b = b + (_⋅_ {b₃ = ℕ.𝐒(ℕ.𝐒 b₃)} a b)

  _𝄩_ : ∀{b₁ b₂ b₃} ⦃ pos : ℕ.Positive(b₃) ⦄ → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₃)
  _𝄩_ {b₃ = ℕ.𝐒 ℕ.𝟎}      _       _       = 𝕟.𝟎
  _𝄩_ {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} 𝕟.𝟎     𝕟.𝟎     = 𝕟.𝟎
  _𝄩_ {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} z@𝕟.𝟎   (𝕟.𝐒 b) = 𝕟.𝐒(z 𝄩 b)
  _𝄩_ {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} (𝕟.𝐒 a) z@𝕟.𝟎   = 𝕟.𝐒(a 𝄩 z)
  _𝄩_ {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} (𝕟.𝐒 a) (𝕟.𝐒 b) = a 𝄩 b

  min : ∀{b₁ b₂ b₃} ⦃ pos : ℕ.Positive(b₃) ⦄ → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₃)
  min {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} (𝕟.𝐒 a) (𝕟.𝐒 b) = 𝕟.𝐒(min a b)
  {-# CATCHALL #-}
  min {b₃ = ℕ.𝐒 _} _ _ = 𝕟.𝟎

  max : ∀{b₁ b₂ b₃} ⦃ pos : ℕ.Positive(b₃) ⦄ → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₃)
  max {b₃ = ℕ.𝐒 ℕ.𝟎}      _       _       = 𝕟.𝟎
  max {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} 𝕟.𝟎     𝕟.𝟎     = 𝕟.𝟎
  max {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} z@𝕟.𝟎   (𝕟.𝐒 b) = 𝕟.𝐒(max z b)
  max {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} (𝕟.𝐒 a) z@𝕟.𝟎   = 𝕟.𝐒(max a z)
  max {b₃ = ℕ.𝐒 (ℕ.𝐒 b₃)} (𝕟.𝐒 a) (𝕟.𝐒 b) = 𝕟.𝐒(max a b)

module Conditional where
  𝐒 : ∀{b} → (n : 𝕟(b)) → ⦃ _ : IsTrue(ℕ.𝐒(𝕟-to-ℕ (n)) ℕ.<? b) ⦄ → 𝕟(b)
  𝐒 {ℕ.𝐒(ℕ.𝐒(b))} (𝕟.𝟎)    = 𝕟.𝐒(𝕟.𝟎)
  𝐒 {ℕ.𝐒(ℕ.𝐒(b))} (𝕟.𝐒(n)) = 𝕟.𝐒(𝐒(n))

module Optional where
  minimum : ∀{n} → Option(𝕟(n))
  minimum{ℕ.𝟎}    = None
  minimum{ℕ.𝐒(_)} = Some 𝕟.minimum

  maximum : ∀{n} → Option(𝕟(n))
  maximum{ℕ.𝟎}    = None
  maximum{ℕ.𝐒(n)} = Some 𝕟.maximum

  _+₀ₗ_ : ∀{b₁ b₂} → Option(𝕟(b₁)) → 𝕟(b₂) → 𝕟(b₁ ℕ.+ b₂)
  _+₀ₗ_      None     𝕟.𝟎      = 𝕟.𝟎
  _+₀ₗ_ {b₁} None     (𝕟.𝐒(b)) = 𝕟.𝐒(_+₀ₗ_ {b₁} None b)
  _+₀ₗ_      (Some a) b        = a Exact.+₀ b

  _+₀ᵣ_ : ∀{b₁ b₂} → 𝕟(b₁) → Option(𝕟(b₂)) → 𝕟(b₁ ℕ.+ b₂)
  _+₀ᵣ_ 𝕟.𝟎      None     = 𝕟.𝟎
  _+₀ᵣ_ (𝕟.𝐒(a)) None     = 𝕟.𝐒(_+₀ᵣ_ a None)
  {-# CATCHALL #-}
  _+₀ᵣ_ a        (Some b) = a Exact.+₀ b

module Unclosed where
  _+ₙₗ_ : ∀{b₂} → (b₁ : ℕ) → 𝕟(b₂) → 𝕟(b₁ ℕ.+ b₂)
  ℕ.𝟎    +ₙₗ b = b
  ℕ.𝐒(a) +ₙₗ b = 𝕟.𝐒(a +ₙₗ b)

  _+ₙᵣ_ : ∀{b₁} → 𝕟(b₁) → (b₂ : ℕ) → 𝕟(b₁ ℕ.+ b₂)
  a +ₙᵣ ℕ.𝟎    = a
  a +ₙᵣ ℕ.𝐒(b) = 𝕟.𝐒(a +ₙᵣ b)

  _ₙ−_ : (x : ℕ) → 𝕟₌(x) → 𝕟₌(x)
  ℕ.𝟎    ₙ− 𝕟.𝟎    = 𝕟.𝟎
  ℕ.𝐒(x) ₙ− 𝕟.𝟎    = 𝕟.𝐒(x ₙ− 𝕟.𝟎)
  ℕ.𝐒(x) ₙ− 𝕟.𝐒(y) = bound-𝐒 (x ₙ− y)

  -- Example: shrink-subtract(5) (7 : 𝕟(6 + 5)) = (2 : 𝕟(6))
  shrink-subtractₗ : ∀{b₁} → (b₂ : ℕ) → 𝕟(ℕ.𝐒(b₁) ℕ.+ b₂) → 𝕟(ℕ.𝐒(b₁))
  shrink-subtractₗ          _        𝕟.𝟎     = 𝕟.𝟎
  shrink-subtractₗ          ℕ.𝟎      (𝕟.𝐒 a) = 𝕟.𝐒 a
  shrink-subtractₗ {ℕ.𝟎}    (ℕ.𝐒 b₂) (𝕟.𝐒 a) = 𝕟.𝟎
  shrink-subtractₗ {ℕ.𝐒 b₁} (ℕ.𝐒 b₂) (𝕟.𝐒 a) = shrink-subtractₗ {ℕ.𝐒 b₁} (b₂) (a)

  shrink-subtractᵣ : (b₁ : ℕ) → ∀{b₂} → 𝕟(b₁ ℕ.+ ℕ.𝐒(b₂)) → 𝕟(ℕ.𝐒(b₂))
  shrink-subtractᵣ _                 𝕟.𝟎     = 𝕟.𝟎
  shrink-subtractᵣ ℕ.𝟎               (𝕟.𝐒 a) = 𝕟.𝐒 a
  shrink-subtractᵣ (ℕ.𝐒 b₁) {ℕ.𝟎}    (𝕟.𝐒 a) = 𝕟.𝟎
  shrink-subtractᵣ (ℕ.𝐒 b₁) {ℕ.𝐒 b₂} (𝕟.𝐒 a) = shrink-subtractᵣ (b₁) {ℕ.𝐒 b₂} (a)

  {-_⋅ₙₗ_ : ∀{b₂} → (b₁ : ℕ) → 𝕟(b₂) → 𝕟(ℕ.𝐒(b₁ ℕ.⋅ b₂))
  _⋅ₙₗ_ {ℕ.𝐒 _} ℕ.𝟎     _ = 𝕟.𝟎
  _⋅ₙₗ_ {ℕ.𝐒 _} (ℕ.𝐒 a) b = {!b Exact.+ (a ⋅ₙₗ b)!}
  -}

  _⋅ₙᵣ_ : ∀{b₁} → 𝕟(b₁) → (b₂ : ℕ) → 𝕟(ℕ.𝐒(b₁ ℕ.⋅ b₂)) -- TODO: Bounds is too great
  _⋅ₙᵣ_ {ℕ.𝐒 _} a ℕ.𝟎     = 𝕟.𝟎
  _⋅ₙᵣ_ {ℕ.𝐒 _} a (ℕ.𝐒 b) = a Exact.+₀ (a ⋅ₙᵣ b)

module Wrapping where
  -- Wrapping subtraction.
  -- Essentially: _[−]_ {b₁}{b₂} a b = (a ℤ.− b) mod b₁
  _[−]_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₁)
  _[−]_ {_}      {ℕ.𝐒 _}  a       𝕟.𝟎     = a
  _[−]_ {ℕ.𝐒 b₁} {ℕ.𝐒 _}  𝕟.𝟎     (𝕟.𝐒 b) = 𝕟.maximum {ℕ.𝐒 b₁} [−] b
  _[−]_ {ℕ.𝐒 b₁} {ℕ.𝐒 b₂} (𝕟.𝐒 a) (𝕟.𝐒 b) = _[−]_ {ℕ.𝐒 b₁}{b₂} (bound-𝐒 a) b

  -- (Flipping around the symmetric point)
  flip : ∀{b} → 𝕟(b) → 𝕟(b)
  flip {ℕ.𝐒(b)} n = 𝕟.maximum{ℕ.𝐒 b} [−] n

  -- Wrapping negation.
  -- Essentially: [−]_ {b} n = (ℤ.− n) mod b
  [−]_ : ∀{b} → 𝕟(b) → 𝕟(b)
  [−]_ {ℕ.𝐒(b)} n = 𝕟.minimum{ℕ.𝐒 b} [−] n

  -- Wrapping addition.
  -- Essentially: _[−]_ {b₁}{b₂} a b = (a ℤ.+ b) mod b₁
  _[+]_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₁)
  _[+]_ {ℕ.𝐒(b₁)} a b = a [−] (𝕟.minimum{ℕ.𝐒(b₁)} [−] b)


  -- Like (_[−]_) but subtracting an ℕ instead.
  _[−ₙ]_ : ∀{n} → 𝕟(n) → ℕ → 𝕟(n)
  _[−ₙ]_ {_}      a       ℕ.𝟎     = a
  _[−ₙ]_ {ℕ.𝐒 n} 𝕟.𝟎     (ℕ.𝐒 b) = 𝕟.maximum {ℕ.𝐒 n} [−ₙ] b
  _[−ₙ]_ {ℕ.𝐒 n} (𝕟.𝐒 a) (ℕ.𝐒 b) = _[−ₙ]_ {ℕ.𝐒 n} (bound-𝐒 a) b

  -- Like (_[+]_) but adding an ℕ instead.
  _[+ₙ]_ : ∀{n} → 𝕟(n) → ℕ → 𝕟(n)
  _[+ₙ]_ {ℕ.𝐒(n)} a b = a [−] (𝕟.minimum{ℕ.𝐒(n)} [−ₙ] b)

  -- Alternative definition of the modulo operator (Alternative to Numeral.Natural.Oper.Modulo._mod_. The algorithm should be similar, but this uses the operators of 𝕟).
  _modₙ_ : ℕ → (m : ℕ) ⦃ pos : ℕ.Positive(m) ⦄ → 𝕟(m)
  a modₙ m = 𝕟.minimum [+ₙ] a

-- (shiftRepeat c) is a mapping that shifts all numbers greater than c downwards.
-- It is similar to the identity mapping but skips 𝐒(c) and instead repeats c.
-- It is more similar to 𝐏 but instead of shifting all numbers down truncating at 0, it only shifts numbers greater than c and truncates at c.
-- Alternative definition by cases:
--   (x ≤ c) → (shiftRepeat c x = id(x))
--   (x > c) → (shiftRepeat c x = 𝐏(x))
-- Examples (Table of n = 4):
--   shiftRepeat{4} 0 0 = 0
--   shiftRepeat{4} 0 1 = 0
--   shiftRepeat{4} 0 2 = 1
--   shiftRepeat{4} 0 3 = 2
--   shiftRepeat{4} 0 4 = 3
--
--   shiftRepeat{4} 1 0 = 0
--   shiftRepeat{4} 1 1 = 1
--   shiftRepeat{4} 1 2 = 1
--   shiftRepeat{4} 1 3 = 2
--   shiftRepeat{4} 1 4 = 3
--
--   shiftRepeat{4} 2 0 = 0
--   shiftRepeat{4} 2 1 = 1
--   shiftRepeat{4} 2 2 = 2
--   shiftRepeat{4} 2 3 = 2
--   shiftRepeat{4} 2 4 = 3
--
--   shiftRepeat{4} 3 0 = 0
--   shiftRepeat{4} 3 1 = 1
--   shiftRepeat{4} 3 2 = 2
--   shiftRepeat{4} 3 3 = 3
--   shiftRepeat{4} 3 4 = 3
shiftRepeat : ∀{n} → 𝕟(n) → (𝕟(ℕ.𝐒(n)) → 𝕟(n))
shiftRepeat {ℕ.𝐒 _} _      𝕟.𝟎      = 𝕟.𝟎
shiftRepeat       𝕟.𝟎      (𝕟.𝐒(x)) = x
shiftRepeat       (𝕟.𝐒(c)) (𝕟.𝐒(x)) = 𝕟.𝐒(shiftRepeat c x)

-- (shiftSkip c) is a mapping that shifts all numbers greater than c downwards.
-- It is functionally equivalent to shiftRepeat, but instead skips the case of (c = x).
shiftSkip :  ∀{n} → (c : 𝕟(ℕ.𝐒(n))) → (x : 𝕟(ℕ.𝐒(n))) → .⦃ c 𝕟.≢ x ⦄ → 𝕟(n)
shiftSkip {ℕ.𝟎}   (𝕟.𝐒(c)) 𝕟.𝟎      = c
shiftSkip {ℕ.𝐒 _} _        𝕟.𝟎      = 𝕟.𝟎
shiftSkip {ℕ.𝐒 _} 𝕟.𝟎      (𝕟.𝐒(x)) = x
shiftSkip {ℕ.𝐒 _} (𝕟.𝐒(c)) (𝕟.𝐒(x)) = 𝕟.𝐒(shiftSkip c x)

shiftRepeat' : ∀{n} ⦃ pos : ℕ.Positive(n) ⦄ → 𝕟(ℕ.𝐒(n)) → (𝕟(ℕ.𝐒(n)) → 𝕟(n))
shiftRepeat' {ℕ.𝐒 ℕ.𝟎}    _        _        = 𝕟.𝟎
shiftRepeat' {ℕ.𝐒(ℕ.𝐒 _)} _        𝕟.𝟎      = 𝕟.𝟎
shiftRepeat' {ℕ.𝐒(ℕ.𝐒 _)} 𝕟.𝟎      (𝕟.𝐒(x)) = x
shiftRepeat' {ℕ.𝐒(ℕ.𝐒 _)} (𝕟.𝐒(c)) (𝕟.𝐒(x)) = 𝕟.𝐒(shiftRepeat' c x)

