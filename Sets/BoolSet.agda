module Sets.BoolSet {ℓ₁} where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Boolean.Theorems
import      Data.List as List
open import Logic.Propositional
open import Functional
open import Operator.Equals
open import Relator.Equals{ℓ₁}{Lvl.𝟎}
open import Relator.Equals.Theorems{ℓ₁}{Lvl.𝟎}
open import Type

record BoolSet{ℓ₂}(T : Type{ℓ₂}) : Type{ℓ₂} where
  field
    inclusion-fn : T → Bool

module _ {ℓ₂}{T : Type{ℓ₂}} where
  𝐔 : BoolSet(T)
  𝐔 = record{inclusion-fn = const(𝑇)}

  ∅ : BoolSet(T)
  ∅ = record{inclusion-fn = const(𝐹)}

  singleton : ⦃ _ : Equals(T) ⦄ → T → BoolSet(T)
  singleton(t) = record{inclusion-fn = (x ↦ x == t)}

  enumeration : ⦃ _ : Equals(T) ⦄ → List.List(T) → BoolSet(T)
  enumeration(l) = record{inclusion-fn = (x ↦ (List.any(t ↦ x == t)(l)))}

  _∈_ : T → BoolSet(T) → Stmt
  _∈_ a set = ((BoolSet.inclusion-fn set a) ≡ 𝑇)

  _∉_ : T → BoolSet(T) → Stmt
  _∉_ a set = (!(BoolSet.inclusion-fn set a) ≡ 𝑇)

  _⊆_ : BoolSet(T) → BoolSet(T) → Stmt
  _⊆_ set₁ set₂ = (∀{a} → (a ∈ set₁) → (a ∈ set₂))

  _⊇_ : BoolSet(T) → BoolSet(T) → Stmt
  _⊇_ set₁ set₂ = _⊆_ set₂ set₁

  _∪_ : BoolSet(T) → BoolSet(T) → BoolSet(T)
  _∪_ A B =
    record{
      inclusion-fn = (elem ↦ BoolSet.inclusion-fn(A)(elem) || BoolSet.inclusion-fn(B)(elem))
    }

  _∩_ : BoolSet(T) → BoolSet(T) → BoolSet(T)
  _∩_ A B =
    record{
      inclusion-fn = (elem ↦ BoolSet.inclusion-fn(A)(elem) && BoolSet.inclusion-fn(B)(elem))
    }

  _∖_ : BoolSet(T) → BoolSet(T) → BoolSet(T)
  _∖_ A B =
    record{
      inclusion-fn = (elem ↦ BoolSet.inclusion-fn(A)(elem) && ! BoolSet.inclusion-fn(B)(elem))
    }

  ∁_ : BoolSet(T) → BoolSet(T)
  ∁_ A =
    record{
      inclusion-fn = (elem ↦ ! BoolSet.inclusion-fn(A)(elem))
    }

  module Theorems where
    [∈]-in-[∪] : ∀{a : T}{S₁ S₂ : BoolSet(T)} → (a ∈ S₁) → (a ∈ (S₁ ∪ S₂))
    [∈]-in-[∪] proof-a = [∨]-introₗ-[𝑇] proof-a

    [∈]-in-[∩] : ∀{a : T}{S₁ S₂ : BoolSet(T)} → (a ∈ S₁) → (a ∈ S₂) → (a ∈ (S₁ ∩ S₂))
    [∈]-in-[∩] proof-a₁ proof-a₂ = [∧]-intro-[𝑇] proof-a₁ proof-a₂

    [∈]-in-[∖] : ∀{a : T}{S₁ S₂ : BoolSet(T)} → (a ∈ S₁) → (a ∉ S₂) → (a ∈ (S₁ ∖ S₂))
    [∈]-in-[∖] proof-a₁ proof-a₂ = [∧]-intro-[𝑇] proof-a₁ proof-a₂

    [∈]-in-[∁] : ∀{a : T}{S : BoolSet(T)} → (a ∉ S) → (a ∈ (∁ S))
    [∈]-in-[∁] = id
