module Structure.Operator.Monoid.Submonoid where

import      Lvl
open import Functional.Instance
open import Logic
open import Logic.Predicate
open import Logic.Predicate.Equiv
open import Sets.PredicateSet renaming (_≡_ to _≡ₛ_)
open import Structure.Setoid
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Operator
open import Type

private variable ℓ ℓₑ ℓₙ₀ : Lvl.Level
private variable T : Type{ℓ}

module _ {ℓₛ} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {_▫_ : T → T → T} (M : Monoid(_▫_)) where
  record Submonoid (S : PredSet{ℓₛ}(T)) : Stmt{Lvl.of(T) Lvl.⊔ ℓₛ} where
    constructor intro
    open Monoid(M) using (id)
    field
      identity-closure : (id ∈ S)
      operator-closure : ∀{x y} → (x ∈ S) → (y ∈ S) → ((x ▫ y) ∈ S)

    Object = ∃(S)

    _▫ₛ_ : Object → Object → Object
    ([∃]-intro x) ▫ₛ ([∃]-intro y) = [∃]-intro (x ▫ y) ⦃ operator-closure infer infer ⦄

    instance
      monoid : Monoid(_▫ₛ_)
      BinaryOperator.congruence                (Monoid.binaryOperator     monoid)   = congruence₂(_▫_)
      Associativity.proof                      (Monoid.associativity      monoid)   = associativity(_▫_)
      ∃.witness                                (Monoid.identity-existence monoid)   = [∃]-intro id ⦃ identity-closure ⦄
      Identityₗ.proof (Identity.left  (∃.proof (Monoid.identity-existence monoid))) = identityₗ(_▫_)(id)
      Identityᵣ.proof (Identity.right (∃.proof (Monoid.identity-existence monoid))) = identityᵣ(_▫_)(id)
