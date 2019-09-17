-- Finite sets represented by lists
module Data.List.Relation.Membership {ℓ} {T : Set(ℓ)} where

import Lvl
open import Functional
open import Data.List
open import Data.List.Proofs
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems using ([↔]-transitivity)
open import Logic.Predicate
open import Numeral.Natural
open import Relator.Equals renaming (_≡_ to _[≡]_ ; _≢_ to _[≢]_)
open import Relator.Equals.Proofs hiding ([≡]-substitutionₗ ; [≡]-substitutionᵣ ; [≡]-reflexivity ; [≡]-transitivity ; [≡]-symmetry)
open import Type

-- The statement of whether an element is in a list
data _∈_ : T → List(T) → Stmt{ℓ} where
  instance
    [∈]-use  : ∀{a}  {L} → (a ∈ (a ⊰ L)) -- Proof of containment when the element is the first element in the list
    [∈]-skip : ∀{a x}{L} → (a ∈ L) → (a ∈ (x ⊰ L)) -- Proof of containment of a longer list when already having a proof of a shorter list

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
