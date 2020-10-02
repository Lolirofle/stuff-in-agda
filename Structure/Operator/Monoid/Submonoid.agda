module Structure.Operator.Monoid.Submonoid where

import      Lvl
open import Logic
open import Logic.Predicate
open import Logic.Predicate.Equiv
open import Sets.PredicateSet
open import Structure.Setoid.WithLvl
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Operator
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}

module _ {ℓₛ} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {_▫_ : T → T → T} (monoid : Monoid(_▫_)) where
  record Submonoid (S : PredSet{ℓₛ}(T)) : Stmt{Lvl.of(T) Lvl.⊔ ℓₛ} where
    constructor intro
    open Monoid(monoid) using (id)
    field
      ⦃ contains-identity ⦄ : (id ∈ S)
      ⦃ operator-closure ⦄  : ∀{x y} → ⦃ x ∈ S ⦄ → ⦃ y ∈ S ⦄ → ((x ▫ y) ∈ S)

    Object = ∃(S)

    _▫ₛ_ : Object → Object → Object
    ([∃]-intro x) ▫ₛ ([∃]-intro y) = [∃]-intro (x ▫ y)

    instance
      is-monoid : Monoid(_▫ₛ_)
      BinaryOperator.congruence (Monoid.binary-operator is-monoid) = congruence₂(_▫_)
      Associativity.proof (Monoid.associativity is-monoid) = associativity(_▫_)
      ∃.witness (Monoid.identity-existence is-monoid) = [∃]-intro id
      Identityₗ.proof (Identity.left (∃.proof (Monoid.identity-existence is-monoid))) = identityₗ(_▫_)(id)
      Identityᵣ.proof (Identity.right (∃.proof (Monoid.identity-existence is-monoid))) = identityᵣ(_▫_)(id)



module _ where
  open import Functional
  open import Function.Equals
  open import Function.Equals.Proofs
  open import Structure.Function
  function-monoid : ⦃ equiv : Equiv{ℓₑ}(T)⦄ ⦃ function : ∀{f : T → T} → Function(f) ⦄ → Monoid(_∘_ {X = T}{Y = T}{Z = T})
  Monoid.binary-operator    function-monoid = [⊜][∘]-binaryOperator
  Monoid.associativity      function-monoid = intro(\{f g h} → [⊜]-associativity {x = f}{y = g}{z = h})
  Monoid.identity-existence function-monoid = [∃]-intro id ⦃ [⊜]-identity ⦄

module _ {ℓₛ} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {_▫_ : T → T → T} (monoid : Monoid(_▫_)) where
  cosetₗ-monoid : ∀{a} → Submonoid(function-monoid)({!a ▫_!})
