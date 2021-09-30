module Structure.Operator.IntegralDomain.Proofs where

open import Functional
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Operator.IntegralDomain
open import Structure.Operator.Properties
open import Structure.Operator.Ring
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ : Lvl.Level

module _ where
  private variable T : Type{ℓ}
  private variable x y : T
