module Numeral.Finite.Bound where

open import Data.Boolean.Stmt
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Comparisons.Proofs

private variable a b n : ℕ

open import Data

boundExact : (i : 𝕟(a)) → (b : ℕ) → .⦃ ord : IsTrue(toℕ i <? b) ⦄ → 𝕟(b)
boundExact 𝟎     (𝐒 _) = 𝟎
boundExact (𝐒 i) (𝐒 b) = 𝐒(boundExact i b)

-- For an arbitrary number `n`, `bound-[≤] n` is the same number as `n` semantically but with a different boundary on the type.
-- Example: bound-[≤?] (3 : 𝕟(10)) = (3 : 𝕟(20))
bound-[≤?] : .⦃ ord : IsTrue(a ≤? b) ⦄ → (𝕟(a) → 𝕟(b))
bound-[≤?] {a}{b} ⦃ ord ⦄ n = boundExact n b ⦃ [<?][≤?]-subtransitivityᵣ{toℕ n}{a} (toℕ-bound{a}{n}) ord ⦄

bound-𝐒 : 𝕟(n) → 𝕟(ℕ.𝐒(n))
bound-𝐒 {n} = bound-[≤?] ⦃ [≤?]-𝐒 {n} ⦄

open import Logic.Propositional
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Decidable
open import Type.Properties.Decidable.Proofs

-- Alternative definition:
--   bound-[≤] {b = 𝐒 b} _        𝟎     = 𝟎
--   bound-[≤] {b = 𝐒 b} (succ p) (𝐒 n) = 𝐒(bound-[≤] p n)
bound-[≤] : (a ≤ b) → (𝕟(a) → 𝕟(b))
bound-[≤] ab = bound-[≤?] ⦃ [↔]-to-[→] decider-true ab ⦄
