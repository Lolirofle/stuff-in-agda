module Numeral.Natural.Prime.Proofs.Representation where

import      Lvl
open import Data.Either as Either using ()
open import Data.Tuple as Tuple using ()
open import Functional
open import Function.Equals
open import Lang.Instance
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.CoordinateVector
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Prime
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Divisibility.Proofs.Product
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator.Equivalence.Proofs
open import Structure.Relator.Properties
open import Structure.Setoid renaming (_≡_ to _≡ₛ_ ; _≢_ to _≢ₛ_)
open import Structure.Setoid.Uniqueness
open import Syntax.Transitivity
open import Type
open import Type.Dependent

private variable a b : ℕ

record PrimePowers(f : ℕ → ℕ) : Type{Lvl.𝟎} where
  constructor intro
  field
    positive-powers : Σ ℕ (n ↦ Vector(n)(ℕ))
    zeroes-correctness : ∀{n} → Positive(f(n)) ↔ ∃(i ↦ (Σ.right positive-powers(i) ≡ n))
    prime-correctness : ∀{i} → Prime(Σ.right positive-powers(i))

  product : ℕ
  product = foldᵣ(_⋅_)(1) (map(n ↦ n ^ f(n)) (Σ.right positive-powers))

  powers-is-positive : ∀{i} → Positive(f(Σ.right positive-powers(i)))
  powers-is-positive = [↔]-to-[←] zeroes-correctness ([∃]-intro _ ⦃ [≡]-intro ⦄)

  -- postulate power-divide-product : ∀{i} → (Σ.right positive-powers i ∣ product)
  {-power-divide-product {pp}{i = 𝟎} = divides-with-[⋅]
    {b = (PrimePowers.positive-powers pp 𝟎) ^ (PrimePowers.power pp (PrimePowers.positive-powers pp 𝟎))}
    {c = foldᵣ(_⋅_)(1) (tail(map(n ↦ n ^ PrimePowers.power pp(n)) (PrimePowers.positive-powers pp)))}
    ([∨]-introₗ (divides-withᵣ-[^] ⦃ PrimePowers.powers-is-positive pp ⦄ (reflexivity(_∣_))))
  power-divide-product {pp}{i = 𝐒 i} = divides-with-[⋅]
    {b = (PrimePowers.positive-powers pp 𝟎) ^ (PrimePowers.power pp (PrimePowers.positive-powers pp 𝟎))}
    {c = foldᵣ(_⋅_)(1) (tail(map(n ↦ n ^ PrimePowers.power pp(n)) (PrimePowers.positive-powers pp)))}
    ([∨]-introᵣ {!!})
  -}

instance
  PrimePowers-equiv : Equiv(∃ PrimePowers)
  Equiv._≡_         PrimePowers-equiv = (_⊜_) on₂ [∃]-witness
  Equiv.equivalence PrimePowers-equiv = on₂-equivalence ⦃ Equiv.equivalence [⊜]-equiv ⦄

{-
-- Each positive number have a corresponding finite multiset of prime numbers such that it is equal to the product of the numbers in the multiset.
-- Examples:
--   n = (p₁ ^ n₁) ⋅ (p₂ ^ n₂) ⋅ … ⋅ (pₖ ^ nₖ)
-- Also called:
-- • Fundamental theorem of arithmetic.
-- • Canonical representation of positive integers by primes.
-- • Unique prime factorization theorem.
prime-representation : ∀{n} → ⦃ pos : Positive(n) ⦄ → ∃! ⦃ PrimePowers-equiv ⦄ (pp ↦ (n ≡ PrimePowers.product pp))
∃.witness (Tuple.left prime-representation) = {!!}
∃.proof (Tuple.left prime-representation) = {!!}
_⊜_.proof (Tuple.right (prime-representation {𝐒 n}) {pp1} {pp2} p1 p2) {p} = {!!}
-}

open import Logic.Classical
open import Numeral.Natural.Decidable
{-
prime-representation : ∀{n} → ⦃ pos : Positive(n) ⦄ → ∃! ⦃ PrimePowers-equiv ⦄ (pp ↦ (n ≡ PrimePowers.product([∃]-proof pp)))
prime-representation {𝐒 n} ⦃ pos ⦄ = [∧]-intro p1 (\{x}{y} → p2{x}{y}) where
  p1 : ∃(pp ↦ (𝐒(n) ≡ PrimePowers.product ([∃]-proof pp)))
  p2 : Unique(pp ↦ (𝐒(n) ≡ PrimePowers.product ([∃]-proof pp)))
  p2 {[∃]-intro x ⦃ ppx ⦄}{[∃]-intro y ⦃ ppy ⦄} px py with PrimePowers.positive-powers ppx | PrimePowers.positive-powers ppy
  p2 {[∃]-intro x ⦃ ppx ⦄} {[∃]-intro y ⦃ ppy ⦄} px py | intro 𝟎 b | intro 𝟎 d = intro {!!}
  p2 {[∃]-intro x ⦃ ppx ⦄} {[∃]-intro y ⦃ ppy ⦄} px py | intro 𝟎 b | intro (𝐒 c) d = {!!}
  p2 {[∃]-intro x ⦃ ppx ⦄} {[∃]-intro y ⦃ ppy ⦄} px py | intro (𝐒 a) b | intro 𝟎 d = {!!}
  p2 {[∃]-intro x ⦃ ppx ⦄} {[∃]-intro y ⦃ ppy ⦄} px py | intro (𝐒 a) b | intro (𝐒 c) d = {!!}
--    let xy = symmetry(_≡_) px 🝖 py
--    in intro \{p} → {!PrimePowers.power-divide-product ppx!}
-}
