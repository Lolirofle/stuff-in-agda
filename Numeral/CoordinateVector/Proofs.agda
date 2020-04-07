module Numeral.CoordinateVector.Proofs where

import      Lvl
open import Data.Boolean
open import Functional
open import Function.Equals
open import Function.Names
open import Logic.Propositional
open import Numeral.CoordinateVector
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Finite.Oper
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Natural
open import Sets.Setoid
-- open import Structure.Function.Domain
open import Structure.Function.Multi
open import Structure.Operator.Names -- Properties
open import Structure.Relator.Properties
open import Type

module _ {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ where
  transfer-elem : ∀{n} → T → Vector(n)(T)
  transfer-elem {n}(x) = fill(x)

  transfer-fn : ∀{n} → (T → T) → (Vector(n)(T) → Vector(n)(T))
  transfer-fn{n}(f) = map(f){n}

  transfer-op : ∀{n} → (T → T → T) → (Vector(n)(T) → Vector(n)(T) → Vector(n)(T))
  transfer-op {n}(_▫_) = map₂(_▫_)

  private variable _▫_ : T → T → T

  transfer-identityₗ : ∀{id} → Identityₗ(_▫_)(id) → ∀{n} → Identityₗ(transfer-op{n}(_▫_))(transfer-elem{n}(id))
  transfer-identityₗ {id} (identity) = intro(identity)

  transfer-identityᵣ : ∀{id} → Identityᵣ(_▫_)(id) → ∀{n} → Identityᵣ(transfer-op{n}(_▫_))(transfer-elem{n}(id))
  transfer-identityᵣ {id} (identity) = intro(identity)

  transfer-identity : ∀{id} → Identity(_▫_)(id) → ∀{n} → Identity(transfer-op{n}(_▫_))(transfer-elem{n}(id))
  transfer-identity {id} ([∧]-intro identityₗ identityᵣ) = [∧]-intro (intro(identityₗ)) (intro(identityᵣ))

  transfer-inverseₗ : ∀{id}{inv} → InverseFunctionₗ(_▫_)(id)(inv) → ∀{n} → InverseFunctionₗ(transfer-op{n}(_▫_))(transfer-elem{n}(id))(transfer-fn{n}(inv))
  transfer-inverseₗ {id}{inv} (inverse) {n} = intro(inverse)

  transfer-inverseᵣ : ∀{id}{inv} → InverseFunctionᵣ(_▫_)(id)(inv) → ∀{n} → InverseFunctionᵣ(transfer-op{n}(_▫_))(transfer-elem{n}(id))(transfer-fn{n}(inv))
  transfer-inverseᵣ {id}{inv} (inverse) {n} = intro(inverse)

  transfer-inverse : ∀{id}{inv} → InverseFunction(_▫_)(id)(inv) → ∀{n} → InverseFunction(transfer-op{n}(_▫_))(transfer-elem{n}(id))(transfer-fn{n}(inv))
  transfer-inverse {id}{inv} ([∧]-intro inverseₗ inverseᵣ) {n} = [∧]-intro (intro(inverseₗ)) (intro(inverseᵣ))

  transfer-associativity : Associativity(_▫_) → ∀{n} → Associativity(transfer-op{n}(_▫_))
  transfer-associativity (associativity) {n} = intro(associativity)

  transfer-preserves : ∀{n} → Names.Preserving₂(transfer-elem{n}) (_▫_) (transfer-op{n}(_▫_))
  _⊜_.proof (transfer-preserves {n = n} {x} {y}) {i} = reflexivity(_≡_)
  -- ∀{x y} → (fill(x ▫ y) ≡ fill(x) 〔 map₂ (_▫_) {n} 〕 fill(y))

  -- transfer-opposite-elem : ∀{n} → 𝕟(n) → Vector(n)(T) → T
  -- transfer-opposite-elem {n}(i)(x) = Vector.proj(n)(i)

  -- transfer-opposite-preserves : ∀{n}{i} → Preserving2(transfer-opposite-elem{n}(i)) (transfer-op{n}(_▫_)) (_▫_)

  -- record PositionVector :  where
