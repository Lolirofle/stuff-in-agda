module Numeral.Natural.Decidable where

open import Logic.Predicate
open import Logic.Propositional.Theorems
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Proofs
open import Operator.Equals
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
open import Type.Properties.Decidable
import      Type.Properties.Decidable.Functions as Decider

instance
  [≡?]-decider : EquivDecider(_≡?_)
  [≡?]-decider {𝟎}  {𝟎}   = true [≡]-intro
  [≡?]-decider {𝟎}  {𝐒 y} = false \()
  [≡?]-decider {𝐒 x}{𝟎}   = false \()
  [≡?]-decider {𝐒 x}{𝐒 y} = Decider.mapProp (congruence₁(𝐒)) (contrapositiveᵣ(injective(𝐒))) ([≡?]-decider {x}{y})

instance
  ℕ-decidable-equiv : EquivDecidable(ℕ)
  ℕ-decidable-equiv = [∃]-intro(_≡?_)

zero?-decider : Decider(1)(_≡ 𝟎)(zero?)
zero?-decider {𝟎}   = true [≡]-intro
zero?-decider {𝐒 x} = false \()
