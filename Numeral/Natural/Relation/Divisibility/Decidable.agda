module Numeral.Natural.Relation.Divisibility.Decidable where

open import Data
open import Functional
open import Lang.Inspect
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Divisibility
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Modulo.Proofs
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator.Properties
open import Type.Properties.Decidable

instance
  [∣]-decider : Decider(2)(_∣_)(_∣₀?_)
  [∣]-decider {𝟎} {𝟎}   = true Div𝟎
  [∣]-decider {𝟎} {𝐒 y} = false [0]-divides-not
  [∣]-decider {𝐒 x} {y} with y mod 𝐒(x) | inspect(\x → y mod 𝐒(x)) x
  ... | 𝟎   | intro eq = true  ([↔]-to-[→] mod-divisibility eq)
  ... | 𝐒 _ | intro eq = false ([𝐒]-not-0 ∘ transitivity(_≡_) (symmetry(_≡_) eq) ∘ [↔]-to-[←] mod-divisibility)
