open import Type

module Relator.Sets {ℓ ℓₑ ℓₛ} {E : Type{ℓₑ}} {S : Type{ℓₛ}} (_∈_ : E → S → Type{ℓ}) where

open import Functional
open import Logic.Propositional
open import Logic.Predicate

_∉_ : E → S → Type
_∉_ = (¬_) ∘₂ (_∈_)

_∋_ : S → E → Type
_∋_ = swap(_∈_)

_∌_ : S → E → Type
_∌_ = (¬_) ∘₂ (_∋_)

_⊆_ : S → S → Type
_⊆_ L₁ L₂ = ∀ₗ(x ↦ ((_→ᶠ_) on₂ (x ∈_)) L₁ L₂)

_⊇_ : S → S → Type
_⊇_ L₁ L₂ = ∀ₗ(x ↦ ((_←_) on₂ (x ∈_)) L₁ L₂)

_≡_ : S → S → Type
_≡_ L₁ L₂ = ∀ₗ(x ↦ ((_↔_) on₂ (x ∈_)) L₁ L₂)

_⊈_ : S → S → Type
_⊈_ = (¬_) ∘₂ (_⊆_)

_⊉_ : S → S → Type
_⊉_ = (¬_) ∘₂ (_⊇_)

_≢_ : S → S → Type
_≢_ = (¬_) ∘₂ (_≡_)
