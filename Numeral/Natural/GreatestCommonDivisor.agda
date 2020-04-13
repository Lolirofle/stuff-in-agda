module Numeral.Natural.GreatestCommonDivisor where

import Lvl
open import Data
open import Numeral.Integer as ℤ
  using (ℤ)
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order
open import Type

{-# TERMINATING #-}
gcd : ℕ → ℕ → ℕ
gcd(a)(𝟎) = a
gcd(a)(𝐒(b)) = gcd(𝐒(b))(a mod 𝐒(b))

lcm : ℕ → ℕ → ℕ
lcm(a)(b) = (a ⋅ b) ⌊/⌋₀ gcd(a)(b)

-- TODO: Prove (gcd(a)(b) ∣ a) and (gcd(a)(b) ∣ b)

data Gcd : ℕ → ℕ → ℕ → Type{Lvl.𝟎} where
  GcdBase : ∀{a} → Gcd a 𝟎 a
  GcdStep : ∀{a b c} → ⦃ _ : (a ≥ b) ⦄ → Gcd a (𝐒(b)) c → Gcd (𝐒(b)) (a mod (𝐒(b))) c
  GcdSwap : ∀{a b c} → ⦃ _ : (a < b) ⦄ → Gcd a (𝐒(b)) c → Gcd (𝐒(b)) a c

open import Relator.Equals
-- open import Structure.Setoid.Uniqueness

-- Gcd-𝟎 : ∀{a b c}{obj : Gcd a 𝟎 c} → (obj ≡ GcdBase{a})

{-
Gcd-unique : ∀{a b c₁ c₂} → Gcd a b c₁ → Gcd a b c₂ → (c₁ ≡ c₂)
Gcd-unique {a} {.0} {.a} {.a} GcdBase GcdBase = {!!}
Gcd-unique {.(𝐒 _)} {.([ 0 , _ ] _ mod' _)} {c₁} {c₂} (GcdStep x) y = {!!}
Gcd-unique {.(𝐒 _)} {b} {c₁} {c₂} (GcdSwap x) y = {!!}
-}
