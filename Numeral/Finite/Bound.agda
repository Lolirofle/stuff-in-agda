module Numeral.Finite.Bound where

open import Lang.Instance
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs

-- For an arbitrary number `n`, `bound-[≤] n` is the same number as `n` semantically but with a different boundary on the type.
-- Example: bound-[≤] p (3: 𝕟(10)) = 3: 𝕟(20) where p: (10 ≤ 20)
bound-[≤] : ∀{a b} → (a ≤ b) → (𝕟(a) → 𝕟(b))
bound-[≤] {𝐒 a} {𝐒 b} _        𝟎     = 𝟎
bound-[≤] {𝐒 a} {𝐒 b} (succ p) (𝐒 n) = 𝐒(bound-[≤] p n)

bound-𝐒 : ∀{n} → 𝕟(n) → 𝕟(ℕ.𝐒(n))
bound-𝐒 = bound-[≤] [≤]-of-[𝐒]

bound-exact : ∀{a b} → (i : 𝕟(a)) → (𝕟-to-ℕ i < b) → 𝕟(b)
bound-exact {𝐒 a} {𝐒 b} 𝟎     (succ _) = 𝟎
bound-exact {𝐒 a} {𝐒 b} (𝐒 i) (succ p) = 𝐒(bound-exact i p)
