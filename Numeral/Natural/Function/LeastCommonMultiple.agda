module Numeral.Natural.Function.LeastCommonMultiple where

import Lvl
open import Functional
open import Numeral.CoordinateVector as Vector using (Vector)
open import Numeral.Finite using (𝕟 ; 𝟎 ; 𝐒)
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Relation.Divisibility
open import Type

-- The least common multiple (lcm) is defined by
lcm : ℕ → ℕ → ℕ
lcm a b = (a ⋅ b) ⌊/⌋₀ gcd(a)(b)

-- The least common multiple of a list of numbers `v` is a number `M` such that it is divisible by all numbers in `v`, and is the smallest one.
record LeastCommonMultiple(n : ℕ) (v : Vector(n)(ℕ)) (M : ℕ) : Type{Lvl.𝟎} where
  constructor intro
  field
    multiple : ∀(i) → (v(i) ∣ M)
    minimum  : ∀{m} → (∀(i) → (v(i) ∣ m)) → (M ∣ m)

-- `Lcm a b M` is the specialization for 2 elements and states that `M` is a multiple of both `a` and `b`, and the smallest one of them.
-- Example:
--   360  = 2³ ⋅ 3² ⋅ 5¹
--   8400 = 2⁴ ⋅ 3¹ ⋅ 5² ⋅ 7¹
--   Lcm 360 8400 = {min(Multiple(360) ∩ Multiple(8400))} = 2⁴ ⋅ 3² ⋅ 5² ⋅ 7¹ = 25200
--   Multiple of first : 360 ⋅ 2¹ ⋅ 5¹ ⋅ 7¹ = 360 ⋅ 70 = 25200
--   Multiple of second: 8400 ⋅ 3¹ = 25200
Lcm = LeastCommonMultiple(2) ∘₂ Vector.pair
module Lcm {a b M} where
  intro₂ : _ → _ → (∀{m} → _ → _ → (M ∣ m)) → Lcm a b M
  intro₂ multipleₗ multipleᵣ minimum = intro{2}{Vector.pair a b}
    (\{𝟎 → multipleₗ ; (𝐒(𝟎)) → multipleᵣ})
    (\dv → minimum (dv 𝟎) (dv (𝐒 𝟎)))
  module _ (inst : Lcm a b M) where
    open LeastCommonMultiple(inst) public
    multipleₗ = multiple 𝟎
    multipleᵣ = multiple(𝐒 𝟎)
    minimum₂ = \{m} a b → minimum{m} \{𝟎 → a ; (𝐒(𝟎)) → b}
