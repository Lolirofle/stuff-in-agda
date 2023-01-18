module Numeral.Finite.Functions where

import Lvl
open import Syntax.Number
open import Functional.Instance
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Natural hiding (𝐏)
import      Numeral.Natural.Function as ℕ
import      Numeral.Natural.Function.Proofs as ℕ
open import Numeral.Natural.Oper

-- Maximum function.
-- Returns the greatest number.
max : ∀{a b} → 𝕟(a) → 𝕟(b) → 𝕟(ℕ.max a b)
max        𝟎      𝟎      = 𝟎
max {a}{b} (𝐒(x)) 𝟎      = bound-[≤] ([∧]-elimₗ (ℕ.max-order {a}{b})) (𝐒(x))
max {a}{b} 𝟎      (𝐒(y)) = bound-[≤] ([∧]-elimᵣ (ℕ.max-order {a}{b})) (𝐒(y))
max        (𝐒(x)) (𝐒(y)) = 𝐒(max x y)

-- Minimum function.
-- Returns the smallest number.
min : ∀{a b} → 𝕟(a) → 𝕟(b) → 𝕟(ℕ.min a b)
min 𝟎      𝟎      = 𝟎
min (𝐒(_)) 𝟎      = 𝟎
min 𝟎      (𝐒(_)) = 𝟎
min (𝐒(x)) (𝐒(y)) = 𝐒(min x y)

{-
import      Numeral.Natural.Relation.Order as ℕ using (_≤_)
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Operator.Properties
open import Structure.Relator.Properties

min₌ : ∀{n} → 𝕟(n) → 𝕟(n) → 𝕟(n)
min₌ x y = bound-[≤] (sub₂(_≡_)(ℕ._≤_) (idempotence(ℕ.min))) (min x y)
-}

max₌ : ∀{n} → 𝕟(n) → 𝕟(n) → 𝕟(n)
max₌ 𝟎      𝟎      = 𝟎
max₌ (𝐒(x)) 𝟎      = 𝐒(x)
max₌ 𝟎      (𝐒(y)) = 𝐒(y)
max₌ (𝐒(x)) (𝐒(y)) = 𝐒(max₌ x y)

min₌ : ∀{n} → 𝕟(n) → 𝕟(n) → 𝕟(n)
min₌ 𝟎      𝟎      = 𝟎
min₌ (𝐒(_)) 𝟎      = 𝟎
min₌ 𝟎      (𝐒(_)) = 𝟎
min₌ (𝐒(x)) (𝐒(y)) = 𝐒(min₌ x y)

boundDiff : ∀{n} → 𝕟(n) → ℕ
boundDiff{𝐒(N)} 𝟎     = 𝐒(N)
boundDiff{𝐒(N)} (𝐒 n) = boundDiff{N} n
