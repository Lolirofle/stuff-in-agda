module Numeral.Finite.Oper where

open import Data
open import Data.Boolean.Stmt
open import Data.Option
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
open import Numeral.Finite as 𝕟 using (𝕟 ; 𝕟₌ ; 𝕟-to-ℕ)
open import Numeral.Finite.Bound
open import Numeral.Natural hiding (𝟎 ; 𝐒 ; 𝐏)
open import Numeral.Natural.Function
open import Numeral.Natural.Function.Proofs
import      Numeral.Natural.Oper as ℕ
import      Numeral.Natural.Oper.Comparisons as ℕ
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Syntax.Number

module Exact where
  -- Predecessor bounded at the minimum (0) for both the value and the maximum.
  -- Example: (𝐏₀(5): 𝕟(8)) = (4: 𝕟(7))
  𝐏₀ : ∀{n} → 𝕟(ℕ.𝐒(ℕ.𝐒(n))) → 𝕟(ℕ.𝐒(n))
  𝐏₀(𝕟.𝟎)    = 𝕟.𝟎
  𝐏₀(𝕟.𝐒(n)) = n

  -- Addition for both the value and the maximum.
  -- Example: (5: 𝕟(8)) + (4: 𝕟(6)) = ((5+4): 𝕟(8+6)) = (9: 𝕟(14))
  _+_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₁ ℕ.+ b₂)
  _+_ {ℕ.𝐒(b₁)}{ℕ.𝐒(b₂)} 𝕟.𝟎      𝕟.𝟎      = 𝕟.𝟎
  _+_ {ℕ.𝐒(b₁)}{ℕ.𝐒(b₂)} 𝕟.𝟎      (𝕟.𝐒(b)) = 𝕟.𝐒(𝕟.𝟎{b₁} + b)
  _+_ {ℕ.𝐒(b₁)}{ℕ.𝐒(b₂)} (𝕟.𝐒(a)) b        = 𝕟.𝐒(a + b)

  -- Distance between two numbers.
  -- Examples:
  --   (3: 𝕟(8)) 𝄩 (5: 𝕟(6)) = ((3𝄩5): 𝕟(max 8 6)) = (2: 𝕟(8))
  --   (5: 𝕟(8)) 𝄩 (3: 𝕟(6)) = ((5𝄩3): 𝕟(max 8 6)) = (2: 𝕟(8))
  --   (7: 𝕟(8)) 𝄩 (0: 𝕟(6)) = ((7𝄩0): 𝕟(max 8 6)) = (7: 𝕟(8))
  _𝄩_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(max b₁ b₂)
  _𝄩_ {ℕ.𝐒 b₁}       {ℕ.𝐒 b₂}       𝕟.𝟎     𝕟.𝟎     = 𝕟.𝟎
  _𝄩_ {ℕ.𝐒 ℕ.𝟎}      {ℕ.𝐒 b₂}       𝕟.𝟎     (𝕟.𝐒 b) = 𝕟.𝐒 b
  _𝄩_ {ℕ.𝐒 (ℕ.𝐒 b₁)} {ℕ.𝐒 b₂}       𝕟.𝟎     (𝕟.𝐒 b) = 𝕟.𝐒(𝕟.𝟎 𝄩 b)
  _𝄩_ {ℕ.𝐒 b₁}       {ℕ.𝐒 b₂}       (𝕟.𝐒 a) (𝕟.𝐒 b) = bound-𝐒(a 𝄩 b)
  _𝄩_ {ℕ.𝐒 b₁}       {ℕ.𝐒 ℕ.𝟎}      (𝕟.𝐒 a) 𝕟.𝟎     = 𝕟.𝐒 a
  _𝄩_ {ℕ.𝐒 b₁}       {ℕ.𝐒 (ℕ.𝐒 b₂)} (𝕟.𝐒 a) 𝕟.𝟎     = 𝕟.𝐒(a 𝄩 𝕟.𝟎)

  _⋅_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₁ ℕ.⋅ b₂)
  _⋅_ {ℕ.𝐒 b₁} {ℕ.𝐒 b₂} a 𝕟.𝟎     = 𝕟.𝟎
  _⋅_ {ℕ.𝐒 b₁} {ℕ.𝐒 b₂} a (𝕟.𝐒 b) = a + (a ⋅ b)

module Bounded where
  -- Predecessor bounded at the minimum (0) for the value only.
  -- Example: (𝐏₀(5): 𝕟(8)) = (4: 𝕟(8))
  𝐏₀ : ∀{n} → 𝕟(n) → 𝕟(n)
  𝐏₀ {ℕ.𝐒(b)} (𝕟.𝟎)         = 𝕟.𝟎
  𝐏₀ {ℕ.𝐒(b)} (𝕟.𝐒(𝕟.𝟎))    = 𝕟.𝟎
  𝐏₀ {ℕ.𝐒(b)} (𝕟.𝐒(𝕟.𝐒(n))) = 𝕟.𝐒(𝐏₀ {b} (𝕟.𝐒(n)))

module Total where
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
  _+₀ₗ_      (Some a) b        = a Exact.+ b

  _+₀ᵣ_ : ∀{b₁ b₂} → 𝕟(b₁) → Option(𝕟(b₂)) → 𝕟(b₁ ℕ.+ b₂)
  _+₀ᵣ_ 𝕟.𝟎      None     = 𝕟.𝟎
  _+₀ᵣ_ (𝕟.𝐒(a)) None     = 𝕟.𝐒(_+₀ᵣ_ a None)
  {-# CATCHALL #-}
  _+₀ᵣ_ a        (Some b) = a Exact.+ b

module Unclosed where
  _+ₙₗ_ : ∀{b₂} → (b₁ : ℕ) → 𝕟(b₂) → 𝕟(b₁ ℕ.+ b₂)
  ℕ.𝟎    +ₙₗ b = b
  ℕ.𝐒(a) +ₙₗ b = 𝕟.𝐒(a +ₙₗ b)

  _+ₙᵣ_ : ∀{b₁} → 𝕟(b₁) → (b₂ : ℕ) → 𝕟(b₁ ℕ.+ b₂)
  a +ₙᵣ ℕ.𝟎    = a
  a +ₙᵣ ℕ.𝐒(b) = 𝕟.𝐒(a +ₙᵣ b)

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
  _⋅ₙᵣ_ {ℕ.𝐒 _} a (ℕ.𝐒 b) = a Exact.+ (a ⋅ₙᵣ b)

module Wrapping where
  -- Wrapping subtraction.
  -- Essentially: _[−]_ {b₁}{b₂} a b = (a −ℤ b) mod b₁
  _[−]_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₁)
  _[−]_ {_}      {ℕ.𝐒 _}  a       𝕟.𝟎     = a
  _[−]_ {ℕ.𝐒 b₁} {ℕ.𝐒 _}  𝕟.𝟎     (𝕟.𝐒 b) = 𝕟.maximum {b₁} [−] b
  _[−]_ {ℕ.𝐒 b₁} {ℕ.𝐒 b₂} (𝕟.𝐒 a) (𝕟.𝐒 b) = _[−]_ {ℕ.𝐒 b₁}{b₂} (bound-𝐒 a) b

  -- Wrapping negation (Flipping around the symmetric point).
  -- Essentially: [−]_ {b} n = (−ℤ n) mod b
  [−]_ : ∀{b} → 𝕟(b) → 𝕟(b)
  [−]_ {ℕ.𝐒 b} n = 𝕟.maximum {b} [−] n

{- TODO: Cannot solve first. Unsure why
[𝐒]-not-0 : ∀{b : ℕ}{n : 𝕟(ℕ.𝐒(b))} → (𝐒{b}(n) ≢ 𝟎{ℕ.𝐒(b)})
[𝐒]-not-0 ()

𝐏keep : ∀{b} → (n : 𝕟(𝐒(b))) → ⦃ _ : n ≢ 𝟎 ⦄ → 𝕟(𝐒(b))
𝐏keep {ℕ.𝟎}    (𝟎)       ⦃ proof ⦄ with proof([≡]-intro)
... | ()
𝐏keep {ℕ.𝐒(b)} (𝟎)       ⦃ _ ⦄     = 𝟎
𝐏keep {ℕ.𝐒(b)} (𝐒(𝟎))    ⦃ _ ⦄     = 𝟎
𝐏keep {ℕ.𝐒(b)} (𝐒(𝐒(n))) ⦃ proof ⦄ = 𝐒(𝐏keep {b} (𝐒(n)) ⦃ [𝐒]-not-0 ⦄)
-}

-- _ : ∀{b} → (n : 𝕟(b)) → (𝕟-to-ℕ (n) < b)

-- _+small_ : ∀{b₁ b₂} → (x : 𝕟(𝐒(b₁))) → (y : 𝕟(𝐒(b₂))) → 𝕟(ℕ.𝐒(𝕟-to-ℕ (x) ℕ.+ 𝕟-to-ℕ (y)))
-- _+small_      𝟎       𝟎      = 𝟎
-- _+small_ {b₁} (𝐒(a))  𝟎      = 𝐒(a +small 𝟎)
-- _+small_      a       (𝐒(b)) = 𝐒(a +small b)

-- _−small_ : ∀{b} → (x : 𝕟(𝐒(b))) → (y : 𝕟(ℕ.𝐒(𝕟-to-ℕ (x)))) → 𝕟(ℕ.𝐒(𝕟-to-ℕ (x) ℕ.−₀ 𝕟-to-ℕ (y)))
-- 𝟎    −small 𝟎    = 𝟎
-- 𝐒(a) −small 𝟎    = 𝐒(a −small 𝟎)
-- 𝐒(a) −small 𝐒(b) = a −small b

{- TODO: Will not work like this
-- Modulo subtraction.
-- Essentially: a [−] b mod n = (a −ℤ b) mod n
_[−]_mod_ : ℕ → ℕ → (n : ℕ) → 𝕟₌(n)
_    [−] _    mod 𝟎    = 𝟎
𝟎    [−] 𝟎    mod 𝐒(n) = 𝟎
𝐒(a) [−] 𝟎    mod 𝐒(n) = a [−] n mod 𝐒(n)
𝟎    [−] 𝐒(b) mod 𝐒(n) = n [−] b mod 𝐒(n)
𝐒(a) [−] 𝐒(b) mod 𝐒(n) = a [−] b mod 𝐒(n)

open import Data
test1 : [−]_ {4} 1 ≡ 3
test1 = [≡]-intro
-}

-- _−_ : ∀{b} → (x : 𝕟(𝐒(b))) → (y : 𝕟(ℕ.𝐒(𝕟-to-ℕ (x)))) → 𝕟(𝐒(b))
-- 𝟎    − 𝟎    = 𝟎
-- 𝐒(a) − 𝟎    = 𝐒(a)
-- 𝐒(a) − 𝐒(b) = bound-𝐒(a − b)

-- TODO: Wrapping and bounded operations
