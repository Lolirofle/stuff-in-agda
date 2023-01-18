module Numeral.Finite.Equiv2 where

open import Numeral.Finite.Relation.Order
open import Numeral.Finite.Relation.Order.Proofs
open import Numeral.Finite
open import Structure.Setoid as Setoid using (Equiv)
open import Type.Dependent.Sigma
open import Type.Dependent.Sigma.Equiv

instance
  𝕟*-equiv : Equiv(𝕟*)
  𝕟*-equiv = Σᵣ-equiv(_≡_)
    (\{A}{a} → [≡]-reflexivity-raw {A}{a})
    (\{A}{B}{a}{b} → [≡]-symmetry-raw {A}{a}{B}{b})
    (\{A}{B}{C}{a}{b}{c} → [≡]-transitivity-raw {A}{a}{B}{b}{C}{c})

_≡*_ = Equiv._≡_ 𝕟*-equiv

instance
  [≡*]-reflexivity = Equiv.reflexivity 𝕟*-equiv

instance
  [≡*]-symmetry = Equiv.symmetry 𝕟*-equiv

instance
  [≡*]-transitivity = Equiv.transitivity 𝕟*-equiv
