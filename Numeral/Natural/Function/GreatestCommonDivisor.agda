module Numeral.Natural.Function.GreatestCommonDivisor where

import Lvl
open import Functional
open import Numeral.CoordinateVector as Vector using (Vector)
open import Numeral.Finite using (𝕟 ; 𝟎 ; 𝐒)
open import Numeral.Natural
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Function.GreatestCommonDivisor.Algorithm
open import Type

-- TODO: Prove that gcd is the infimum in a lattice of ℕ with divisibility as its ordering

-- An algorithm for computing the greatest common divisor for two numbers.
-- Also called: Euclid's algorithm.
-- Termination: See `Gcd-existence` for a functionally equal variant of this function that passes the termination checker. It is equal in the sense that the same algorithm is used to construct the existence and to compute the value of this function. This is even more evident when looking at `Gcd-gcd`.
-- Alternative implementation:
--   gcd(a)(𝟎) = a
--   gcd(a)(𝐒(b)) with [≥]-or-[<] {a}{𝐒(b)}
--   ... | [∨]-introₗ _ = gcd(𝐒(b))(a mod 𝐒(b))
--   ... | [∨]-introᵣ _ = gcd(𝐒(b))(a)
gcd : ℕ → ℕ → ℕ
gcd = gcdAlgorithm(\_ _ _ → id) id id

-- The greatest common divisor of a list of numbers `v` is a number `D` such that it is a divisor of all numbers in `v`, and the greatest one of them.
record GreatestCommonDivisor(n : ℕ) (v : Vector(n)(ℕ)) (D : ℕ) : Type{Lvl.𝟎} where
  constructor intro
  field
    divisor : ∀(i) → (D ∣ v(i))
    maximum : ∀{d} → (∀(i) → (d ∣ v(i))) → (d ∣ D)

-- `Gcd a b D` is the specialization of `GreatestCommonDivisor` for 2 elements.
-- Example:
--   Divisor(24) = {1,2,3,4,  6,8,   12,      24}
--   Divisor(60) = {1,2,3,4,5,6  ,10,12,15,20,   30,60}
--   24 = 2³ ⋅ 3¹
--   60 = 2² ⋅ 3¹ ⋅ 5¹
--   Gcd 24 60 = {max(Divisor(24) ∩ Divisor(60))} = 2² ⋅ 3¹ = 12
--   Divisor of first : 24 / 12 = 2
--   Divisor of second: 60 / 12 = 5
Gcd = GreatestCommonDivisor(2) ∘₂ Vector.pair
module Gcd {a b D} where
  intro₂ : _ → _ → (∀{d} → _ → _ → (d ∣ D)) → Gcd a b D
  intro₂ divisorₗ divisorᵣ maximum = intro{2}{Vector.pair a b}
    (\{𝟎 → divisorₗ ; (𝐒(𝟎)) → divisorᵣ})
    (\dv → maximum (dv 𝟎) (dv (𝐒 𝟎)))
  module _ (inst : Gcd a b D) where
    open GreatestCommonDivisor(inst) public
    divisorₗ = divisor 𝟎
    divisorᵣ = divisor(𝐒 𝟎)
    maximum₂ = \{d} a b → maximum{d} \{𝟎 → a ; (𝐒(𝟎)) → b}
