module Numeral.Natural.Coprime.Decidable where

open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Coprime
open import Numeral.Natural.Coprime.Proofs
open import Numeral.Natural.Decidable
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Oper.Comparisons
open import Relator.Equals
open import Type.Properties.Decidable
open import Type.Properties.Decidable.Proofs

instance
  Coprime-decider : Decider(2)(Coprime)(\a b → gcd a b ≡? 1)
  Coprime-decider {x}{y} = [↔]-to-[←] (decider-relator Coprime-gcd [≡]-intro) ℕ-equality-decider
