module FnSet where

import      Level as Lvl
open import Boolean
open        Boolean.Operators
open import BooleanTheorems
open import Functional
open import Relator.Equals(Lvl.𝟎)
open import Type

record FnSet(T : Type) : Type where
  field
    inclusion-fn : T → Bool -- TODO: This can probably be expressed in any logic by replacing Bool with the proposition in the logic in question

Universe : ∀{T} → FnSet(T)
Universe = record{inclusion-fn = const(𝑇)}

∅ : ∀{T} → FnSet(T)
∅ = record{inclusion-fn = const(𝐹)}

_∈_ : ∀{T} → T → FnSet(T) → Type
_∈_ a set = ((FnSet.inclusion-fn set a) ≡ 𝑇)

_∉_ : ∀{T} → T → FnSet(T) → Type
_∉_ a set = (¬ (FnSet.inclusion-fn set a) ≡ 𝑇)

_⊆_ : ∀{T} → FnSet(T) → FnSet(T) → Type
_⊆_ set₁ set₂ = (∀{a} → (a ∈ set₁) → (a ∈ set₂))

_⊇_ : ∀{T} → FnSet(T) → FnSet(T) → Type
_⊇_ set₁ set₂ = _⊆_ set₂ set₁

_∪_ : ∀{T} → FnSet(T) → FnSet(T) → FnSet(T)
_∪_ A B =
  record{
    inclusion-fn = (elem ↦ FnSet.inclusion-fn(A)(elem) ∨ FnSet.inclusion-fn(B)(elem))
  }

_∩_ : ∀{T} → FnSet(T) → FnSet(T) → FnSet(T)
_∩_ A B =
  record{
    inclusion-fn = (elem ↦ FnSet.inclusion-fn(A)(elem) ∧ FnSet.inclusion-fn(B)(elem))
  }

_∖_ : ∀{T} → FnSet(T) → FnSet(T) → FnSet(T)
_∖_ A B =
  record{
    inclusion-fn = (elem ↦ FnSet.inclusion-fn(A)(elem) ∧ ¬ FnSet.inclusion-fn(B)(elem))
  }

∁_ : ∀{T} → FnSet(T) → FnSet(T)
∁_ A =
  record{
    inclusion-fn = (elem ↦ ¬ FnSet.inclusion-fn(A)(elem))
  }

module Theorems where
  [∈]-in-[∪] : ∀{T}{a : T}{S₁ S₂ : FnSet(T)} → (a ∈ S₁) → (a ∈ (S₁ ∪ S₂))
  [∈]-in-[∪] proof-a = [∨]-introₗ-[𝑇] proof-a

  [∈]-in-[∩] : ∀{T}{a : T}{S₁ S₂ : FnSet(T)} → (a ∈ S₁) → (a ∈ S₂) → (a ∈ (S₁ ∩ S₂))
  [∈]-in-[∩] proof-a₁ proof-a₂ = [∧]-intro-[𝑇] proof-a₁ proof-a₂

  [∈]-in-[∖] : ∀{T}{a : T}{S₁ S₂ : FnSet(T)} → (a ∈ S₁) → (a ∉ S₂) → (a ∈ (S₁ ∖ S₂))
  [∈]-in-[∖] proof-a₁ proof-a₂ = [∧]-intro-[𝑇] proof-a₁ proof-a₂

  [∈]-in-[∁] : ∀{T}{a : T}{S : FnSet(T)} → (a ∉ S) → (a ∈ (∁ S))
  [∈]-in-[∁] = id
