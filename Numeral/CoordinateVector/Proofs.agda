module Numeral.CoordinateVector.Proofs where

import      Lvl
open import Data.Boolean
import      Functional as Fn
open import Function.Equals
open import Function.Names
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.CoordinateVector
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Finite.Oper
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Natural
open import Structure.Setoid.WithLvl
open import Structure.Operator.Group
open import Structure.Function.Multi
open import Structure.Function
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Properties
open import Type

module _ {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ where
  private variable _▫_ : T → T → T
  private variable inv : T → T
  private variable id : T
  private variable n : ℕ

  instance
    map₂-fill-identityₗ : ⦃ ident : Identityₗ(_▫_)(id) ⦄ → Identityₗ(map₂{d = n}(_▫_))(fill{d = n}(id))
    map₂-fill-identityₗ = intro(intro(identityₗ _ _))

  instance
    map₂-fill-identityᵣ : ⦃ ident : Identityᵣ(_▫_)(id) ⦄ → Identityᵣ(map₂{d = n}(_▫_))(fill{d = n}(id))
    map₂-fill-identityᵣ = intro(intro(identityᵣ _ _))

  instance
    map₂-fill-identity : ⦃ ident : Identity(_▫_)(id) ⦄ → Identity(map₂{d = n}(_▫_))(fill{d = n}(id))
    map₂-fill-identity = intro ⦃ _ ⦄ ⦃ map₂-fill-identityₗ ⦄ ⦃ map₂-fill-identityᵣ ⦄

  instance
    map₂-map-inverseₗ : ⦃ ident : Identityₗ(_▫_)(id) ⦄ ⦃ inver : InverseFunctionₗ(_▫_) ⦃ [∃]-intro _ ⦄ (inv) ⦄ → InverseFunctionₗ(map₂{d = n}(_▫_)) ⦃ [∃]-intro _ ⦄ (map(inv))
    map₂-map-inverseₗ = intro(intro(inverseFunctionₗ _ ⦃ [∃]-intro _ ⦄ _))

  instance
    map₂-map-inverseᵣ : ⦃ ident : Identityᵣ(_▫_)(id) ⦄ ⦃ inver : InverseFunctionᵣ(_▫_) ⦃ [∃]-intro _ ⦄ (inv) ⦄ → InverseFunctionᵣ(map₂{d = n}(_▫_)) ⦃ [∃]-intro _ ⦄ (map(inv))
    map₂-map-inverseᵣ = intro(intro(inverseFunctionᵣ _ ⦃ [∃]-intro _ ⦄ _))

  instance
    map₂-map-inverse : ⦃ ident : Identity(_▫_)(id) ⦄ ⦃ inver : InverseFunction(_▫_) ⦃ [∃]-intro _ ⦄ (inv) ⦄ → InverseFunction(map₂{d = n}(_▫_)) ⦃ [∃]-intro _ ⦄ (map(inv))
    map₂-map-inverse = intro ⦃ _ ⦄ ⦃ _ ⦄ ⦃ map₂-map-inverseₗ ⦄ ⦃ map₂-map-inverseᵣ ⦄

  instance
    map₂-associativity : ⦃ assoc : Associativity(_▫_) ⦄ → Associativity(map₂{d = n}(_▫_))
    map₂-associativity = intro(intro(associativity _))

  instance
    map₂-preserves : Preserving₂(fill) (_▫_) (map₂{d = n}(_▫_))
    map₂-preserves = intro(intro(reflexivity(_≡_)))

  instance
    map-function : ⦃ func : Function(inv) ⦄ → Function(map{d = n}(inv))
    Function.congruence map-function (intro p) = intro (congruence₁ _ p)

  instance
    map₂-binaryOperator : ⦃ oper : BinaryOperator(_▫_) ⦄ → BinaryOperator(map₂{d = n}(_▫_))
    BinaryOperator.congruence map₂-binaryOperator (intro p) (intro q) = intro (congruence₂ _ p q)

  -- map₂ite-elem :{d = n} ∀ → 𝕟(n) → Vector(n)(T) → T
  -- map₂ite{d = n}-elem (i)(x) = Vector.proj(n)(i)

  -- map₂ite-preserves :{d = n} ∀{i} → Preserving2(map₂ite{d = n}-elem(i)) (map₂(_▫_)) (_▫_)

  instance
    map₂-monoid : ⦃ monoid : Monoid(_▫_) ⦄ → Monoid(map₂{d = n}(_▫_))
    Monoid.identity-existence map₂-monoid = [∃]-intro _

  instance
    map₂-group : ⦃ group : Group(_▫_) ⦄ → Group(map₂{d = n}(_▫_))
    Group.monoid map₂-group = map₂-monoid
    Group.inverse-existence map₂-group = [∃]-intro _

