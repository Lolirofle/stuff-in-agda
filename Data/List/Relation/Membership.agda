open import Type

-- Finite sets represented by lists
module Data.List.Relation.Membership {ℓ} {T : Type{ℓ}} where

import Lvl
open import Data.List
open import Logic
open import Logic.Propositional

-- The statement of whether an element is in a list
data _∈_ : T → List(T) → Stmt{ℓ} where
  instance use  : ∀{a}  {L} → (a ∈ (a ⊰ L)) -- Proof of containment when the element is the first element in the list
  instance skip : ∀{a x}{L} → ⦃ _ : (a ∈ L) ⦄ → (a ∈ (x ⊰ L)) -- Proof of containment of a longer list when already having a proof of a shorter list

_∉_ : T → List(T) → Stmt
_∉_ x L = ¬(x ∈ L)

_∋_ : List(T) → T → Stmt
_∋_ L x = (x ∈ L)

_∌_ : List(T) → T → Stmt
_∌_ L x = ¬(L ∋ x)

-- Other relators related to sets

_⊆_ : List(T) → List(T) → Stmt
_⊆_ L₁ L₂ = ∀{x} → (x ∈ L₁) → (x ∈ L₂)

_⊇_ : List(T) → List(T) → Stmt
_⊇_ L₁ L₂ = ∀{x} → (x ∈ L₁) ← (x ∈ L₂)

_≡_ : List(T) → List(T) → Stmt
_≡_ L₁ L₂ = ∀{x} → (x ∈ L₁) ↔ (x ∈ L₂)

_⊈_ : List(T) → List(T) → Stmt
_⊈_ L₁ L₂ = ¬(L₁ ⊆ L₂)

_⊉_ : List(T) → List(T) → Stmt
_⊉_ L₁ L₂ = ¬(L₁ ⊇ L₂)

_≢_ : List(T) → List(T) → Stmt
_≢_ L₁ L₂ = ¬(L₁ ≡ L₂)
