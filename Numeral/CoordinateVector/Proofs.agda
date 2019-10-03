module Numeral.CoordinateVector.Proofs {ℓₗ}{ℓₒ} where

import      Lvl
open import Data.Boolean
open import Functional
open import Functional.Equals
open import Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ}
open import Numeral.CoordinateVector{ℓₒ}
open import Numeral.CoordinateVector.Equals
open import Numeral.Finite
open import Numeral.Finite.Bound{ℓₒ}
open import Numeral.Finite.Oper
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Natural
open import Sets.Setoid{ℓₗ}
open import Structure.Function.Domain{ℓₗ}
open import Structure.Operator.Properties{ℓₗ}{ℓₒ}
open import Structure.Relator.Properties{ℓₗ}{ℓₒ}
open import Type{ℓₒ}

module _ {T : Type} ⦃ _ : Equiv(T) ⦄ {_▫_ : T → T → T} where
  transfer-elem : ∀{n} → T → Vector(n)(T)
  transfer-elem {n}(x) = fill(x){n}

  transfer-fn : ∀{n} → (T → T) → (Vector(n)(T) → Vector(n)(T))
  transfer-fn{n}(f) = map(f){n}

  transfer-op : ∀{n} → (T → T → T) → (Vector(n)(T) → Vector(n)(T) → Vector(n)(T))
  transfer-op {n}(_▫_) = map₂(_▫_){n}

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

  transfer-preserves : ∀{n} → Preserving2(transfer-elem{n}) (_▫_) (transfer-op{n}(_▫_))
  transfer-preserves{𝟎}    {x}{y} with (Vector.proj(x) | Vector.proj(y))
  ... | ()
  transfer-preserves{𝐒(n)} {x}{y} = [≡]-with() (transfer-preserves{n} {tail x}{tail y})
  -- ∀{x y} → (fill(x ▫ y) ≡ fill(x) 〔 map₂ (_▫_) {n} 〕 fill(y))

  transfer-opposite-elem : ∀{n} → 𝕟(n) → Vector(n)(T) → T
  transfer-opposite-elem {n}(i)(x) = Vector.proj(n)(i)

  -- transfer-opposite-preserves : ∀{n}{i} → Preserving2(transfer-opposite-elem{n}(i)) (transfer-op{n}(_▫_)) (_▫_)
