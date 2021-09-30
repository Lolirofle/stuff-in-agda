module Numeral.Natural.Relation.Order.Decidable where

open import Functional
open import Logic.IntroInstances
open import Logic.Propositional.Theorems
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function.Domain
open import Type.Properties.Decidable

instance
  [≤]-decider : Decider(2)(_≤_)(_≤?_)
  [≤]-decider {𝟎} {𝟎} = true [≤]-minimum
  [≤]-decider {𝟎} {𝐒 y} = true [≤]-minimum
  [≤]-decider {𝐒 x} {𝟎} = false \()
  [≤]-decider {𝐒 x} {𝐒 y} = step{f = id} (true ∘ \p → [≤]-with-[𝐒] ⦃ p ⦄) (false ∘ contrapositiveᵣ [≤]-without-[𝐒]) ([≤]-decider {x}{y})

[<]-decider : Decider(2)(_<_)(_<?_)
[<]-decider {𝟎} {𝟎} = false (λ ())
[<]-decider {𝟎} {𝐒 y} = true (succ min)
[<]-decider {𝐒 x} {𝟎} = false (λ ())
[<]-decider {𝐒 x} {𝐒 y} = step{f = id} (true ∘ succ) (false ∘ contrapositiveᵣ [≤]-without-[𝐒]) ([<]-decider {x} {y})

[≥]-decider : Decider(2)(_≥_)(_≥?_)
[≥]-decider = [≤]-decider

[>]-decider : Decider(2)(_>_)(_>?_)
[>]-decider = [<]-decider
