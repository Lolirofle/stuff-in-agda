module Numeral.Finite.Oper where

import Lvl
open import Syntax.Number
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Natural hiding (𝐏)
open import Numeral.Natural.Function
open import Numeral.Natural.Function.Proofs
import      Numeral.Natural.Oper as ℕ
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs

𝐏₀ : ∀{n} → 𝕟(𝐒(𝐒(n))) → 𝕟(𝐒(n))
𝐏₀(𝟎)    = 𝟎
𝐏₀(𝐒(n)) = n

𝐏₀keep : ∀{n} → 𝕟(n) → 𝕟(n)
𝐏₀keep {ℕ.𝟎}    ()
𝐏₀keep {ℕ.𝐒(b)} (𝟎)       = 𝟎
𝐏₀keep {ℕ.𝐒(b)} (𝐒(𝟎))    = 𝟎
𝐏₀keep {ℕ.𝐒(b)} (𝐒(𝐒(n))) = 𝐒(𝐏₀keep {b} (𝐒(n)))

𝐒keep : ∀{b} → (n : 𝕟(𝐒(b))) → ⦃ _ : ℕ.𝐒 (𝕟-to-ℕ (n)) ≤ b ⦄ → 𝕟(𝐒(b)) -- (n ≢ b) would also work?
𝐒keep {ℕ.𝟎}    (_)    ⦃ ⦄
𝐒keep {ℕ.𝐒(b)} (𝟎)    ⦃ _ ⦄     = 𝐒(𝟎)
𝐒keep {ℕ.𝐒(b)} (𝐒(n)) ⦃ proof ⦄ = 𝐒(𝐒keep {b} (n) ⦃ [≤]-without-[𝐒] {ℕ.𝐒(𝕟-to-ℕ (n))} {b} (proof) ⦄)

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

_+_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₁ ℕ.+ b₂)
_+_ {𝟎} {_}        ()
_+_ {_} {𝟎}        (_) ()
_+_ {𝐒(b₁)}{𝐒(b₂)} 𝟎       𝟎      = 𝟎
_+_ {𝐒(b₁)}{𝐒(b₂)} (𝐒(a))  𝟎      = 𝐒(a + 𝟎{b₂})
_+_ {𝐒(b₁)}{𝐒(b₂)} a       (𝐒(b)) = 𝐒(a + b)

-- Example: shrink-subtract(5) (7 : 𝕟(6 + 5)) = (2 : 𝕟(6))
shrink-subtractₗ : ∀{b₁} → (b₂ : ℕ) → 𝕟(𝐒(b₁) ℕ.+ b₂) → 𝕟(𝐒(b₁))
shrink-subtractₗ        _      𝟎     = 𝟎
shrink-subtractₗ        𝟎      (𝐒 a) = 𝐒 a
shrink-subtractₗ {𝟎}    (𝐒 b₂) (𝐒 a) = 𝟎
shrink-subtractₗ {𝐒 b₁} (𝐒 b₂) (𝐒 a) = shrink-subtractₗ {𝐒 b₁} (b₂) (a)

shrink-subtractᵣ : (b₁ : ℕ) → ∀{b₂} → 𝕟(b₁ ℕ.+ 𝐒(b₂)) → 𝕟(𝐒(b₂))
shrink-subtractᵣ        _      𝟎     = 𝟎
shrink-subtractᵣ        𝟎      (𝐒 a) = 𝐒 a
shrink-subtractᵣ (𝐒 b₁) {𝟎}    (𝐒 a) = 𝟎
shrink-subtractᵣ (𝐒 b₁) {𝐒 b₂} (𝐒 a) = shrink-subtractᵣ (b₁) {𝐒 b₂} (a)

_𝄩_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(max b₁ b₂)
_𝄩_ {𝐒 b₁}     {𝐒 b₂}     𝟎     𝟎     = 𝟎
_𝄩_ {𝐒 𝟎}      {𝐒 b₂}     𝟎     (𝐒 b) = 𝐒 b
_𝄩_ {𝐒 (𝐒 b₁)} {𝐒 b₂}     𝟎     (𝐒 b) = 𝐒(𝟎 𝄩 b)
_𝄩_ {𝐒 b₁}     {𝐒 𝟎}      (𝐒 a) 𝟎     = 𝐒 a
_𝄩_ {𝐒 b₁}     {𝐒 (𝐒 b₂)} (𝐒 a) 𝟎     = 𝐒(a 𝄩 𝟎)
_𝄩_ {𝐒 b₁}     {𝐒 b₂}     (𝐒 a) (𝐒 b) = bound-𝐒(a 𝄩 b)

-- Wrapping subtraction.
-- Essentially: _[−]_ {b₁}{b₂} a b = (a −ℤ b) mod b₁
_[−]_ : ∀{b₁ b₂} → 𝕟(b₁) → 𝕟(b₂) → 𝕟(b₁)
_[−]_ {_}    {𝐒 _}  a     𝟎     = a
_[−]_ {𝐒 b₁} {𝐒 _}  𝟎     (𝐒 b) = maximum {b₁} [−] b
_[−]_ {𝐒 b₁} {𝐒 b₂} (𝐒 a) (𝐒 b) = _[−]_ {𝐒 b₁}{b₂} (bound-𝐒 a) b

-- Wrapping negation (Flipping around the symmetric point).
-- Essentially: [−]_ {b} n = (−ℤ n) mod b
[−]_ : ∀{b} → 𝕟(b) → 𝕟(b)
[−]_ {𝐒 b} n = _[−]_ {𝐒 b}{𝐒 b} 𝟎 n

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
