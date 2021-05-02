module Numeral.Finite.Decidable where

import Lvl
open import Functional
open import Logic.Propositional.Theorems
open import Numeral.Finite
open import Numeral.Finite.Proofs
import      Numeral.Finite.Oper.Comparisons as 𝕟
open import Numeral.Natural
open import Operator.Equals
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function.Domain
open import Type.Properties.Decidable

private variable N : ℕ

instance
  [≡][𝕟]-decider : ∀{n} → EquivDecider(𝕟._≡?_ {n})
  [≡][𝕟]-decider {𝐒 n} {𝟎}   {𝟎}   = true [≡]-intro
  [≡][𝕟]-decider {𝐒 n} {𝟎}   {𝐒 y} = false \()
  [≡][𝕟]-decider {𝐒 n} {𝐒 x} {𝟎}   = false \()
  [≡][𝕟]-decider {𝐒 n} {𝐒 x} {𝐒 y} = step{f = id} (true ∘ [≡]-with(𝐒)) (false ∘ contrapositiveᵣ(injective(𝐒))) ([≡][𝕟]-decider {n} {x} {y})
