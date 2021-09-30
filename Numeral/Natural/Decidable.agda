module Numeral.Natural.Decidable where

open import Data
open import Data.Boolean
open import Functional
open import Lang.Inspect
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
open import Type.Properties.Decidable

instance
  ℕ-equality-decider : Decider(2)(_≡_)(_≡?_)
  ℕ-equality-decider {𝟎}  {𝟎}   = true [≡]-intro
  ℕ-equality-decider {𝟎}  {𝐒 y} = false \()
  ℕ-equality-decider {𝐒 x}{𝟎}   = false \()
  ℕ-equality-decider {𝐒 x}{𝐒 y} = step{f = id} (true ∘ congruence₁(𝐒)) (false ∘ contrapositiveᵣ(injective(𝐒))) (ℕ-equality-decider {x}{y})

zero?-decider : Decider(1)(_≡ 𝟎)(zero?)
zero?-decider {𝟎}   = true [≡]-intro
zero?-decider {𝐒 x} = false \()
