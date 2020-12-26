module Structure.Operator.Monoid.Monoids.Function where

open import Functional
open import Function.Equals
open import Function.Equals.Proofs
import      Lvl
open import Logic
open import Logic.Predicate
open import Structure.Function
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}

function-monoid : ⦃ equiv : Equiv{ℓₑ}(T)⦄ ⦃ function : ∀{f : T → T} → Function(f) ⦄ → Monoid(_∘_ {X = T}{Y = T}{Z = T})
Monoid.binary-operator    function-monoid = [⊜][∘]-binaryOperator
Monoid.associativity      function-monoid = intro(\{f g h} → [⊜]-associativity {x = f}{y = g}{z = h})
Monoid.identity-existence function-monoid = [∃]-intro id ⦃ [⊜]-identity ⦄
