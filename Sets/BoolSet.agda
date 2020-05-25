module Sets.BoolSet {ℓ} where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Logic using (_⟶_ ; _⟵_)
open        Data.Boolean.Operators.Programming hiding (_==_)
open import Data.Boolean.Stmt
open import Data.Boolean.Proofs
import      Data.List as List
import      Data.List.Functions as List
open import Logic
open import Functional
open import Operator.Equals
open import Relator.Equals
open import Type

-- A function from a type T to a boolean value.
-- This can be interpreted as a computable set over T (a set with a computable containment relation).
BoolSet : ∀{ℓ} → Type{ℓ} → Type{ℓ}
BoolSet(T) = (T → Bool)

module _ {T : Type{ℓ}} where
  𝐔 : BoolSet(T)
  𝐔 = const(𝑇)

  ∅ : BoolSet(T)
  ∅ = const(𝐹)

  singleton : ⦃ _ : BoolEquality(T) ⦄ → T → BoolSet(T)
  singleton(t) = (_== t)

  enumeration : ⦃ _ : BoolEquality(T) ⦄ → List.List(T) → BoolSet(T)
  enumeration(l) = (x ↦ List.satisfiesAny(_== x)(l))

  _∈?_ : T → BoolSet(T) → Bool
  _∈?_ = apply

  _∉?_ : T → BoolSet(T) → Bool
  _∉?_ a set = !(a ∈? set)

  {- TODO: Define a FinitelyEnumerable relation
  _⊆?_ : BoolSet(T) → BoolSet(T) → Bool
  _⊆?_ A B = all(elem ↦ (elem ∈? A) ⟶ (elem ∈? B))

  _⊇?_ : BoolSet(T) → BoolSet(T) → Bool
  _⊇?_ A B = all(elem ↦ (elem ∈? A) ⟵ (elem ∈? B))
  -}

  _∈_ : T → BoolSet(T) → Stmt
  _∈_ a set = IsTrue(a ∈? set)

  _∉_ : T → BoolSet(T) → Stmt
  _∉_ a set = IsTrue(a ∉? set)

  _⊆_ : BoolSet(T) → BoolSet(T) → Stmt
  _⊆_ set₁ set₂ = (∀{a} → (a ∈ set₁) → (a ∈ set₂))

  _⊇_ : BoolSet(T) → BoolSet(T) → Stmt
  _⊇_ set₁ set₂ = _⊆_ set₂ set₁

  _∪_ : BoolSet(T) → BoolSet(T) → BoolSet(T)
  _∪_ A B = (elem ↦ (elem ∈? A) || (elem ∈? B))

  _∩_ : BoolSet(T) → BoolSet(T) → BoolSet(T)
  _∩_ A B = (elem ↦ (elem ∈? A) && (elem ∈? B))

  _∖_ : BoolSet(T) → BoolSet(T) → BoolSet(T)
  _∖_ A B = (elem ↦ (elem ∈? A) && !(elem ∈? B))

  ∁_ : BoolSet(T) → BoolSet(T)
  ∁_ A = (elem ↦ !(elem ∈? A))

  ℘_ : BoolSet(T) → BoolSet(BoolSet(T))
  ℘_ _ = const(𝑇)
