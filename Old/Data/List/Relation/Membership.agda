-- Finite sets represented by lists
module Data.List.Relation.Membership {ℓ₁} {ℓ₂} {T : Set(ℓ₂)} where

import Lvl
open import Functional
open import Data.List
open import Data.List.Proofs{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Propositional.Theorems{ℓ₁ Lvl.⊔ ℓ₂} using ([↔]-transitivity)
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Numeral.Natural
open import Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂} renaming (_≡_ to _[≡]_ ; _≢_ to _[≢]_)
open import Relator.Equals.Proofs{ℓ₁} hiding ([≡]-substitutionₗ ; [≡]-substitutionᵣ ; [≡]-reflexivity ; [≡]-transitivity ; [≡]-symmetry)
open import Type{ℓ₂}

-- The statement of whether an element is in a list
data _∈_ : T → List{ℓ₂}(T) → Stmt where
  instance
    [∈]-use  : ∀{a}  {L} → (a ∈ (a ⊰ L)) -- Proof of containment when the element is the first element in the list
    [∈]-skip : ∀{a x}{L} → (a ∈ L) → (a ∈ (x ⊰ L)) -- Proof of containment of a longer list when already having a proof of a shorter list

_∉_ : T → List{ℓ₂}(T) → Stmt
_∉_ x L = ¬(x ∈ L)

_∋_ : List{ℓ₂}(T) → T → Stmt
_∋_ L x = (x ∈ L)

_∌_ : List{ℓ₂}(T) → T → Stmt
_∌_ L x = ¬(L ∋ x)

-- Other relators related to sets

_⊆_ : List{ℓ₂}(T) → List{ℓ₂}(T) → Stmt
_⊆_ L₁ L₂ = ∀{x} → (x ∈ L₁) → (x ∈ L₂)

_⊇_ : List{ℓ₂}(T) → List{ℓ₂}(T) → Stmt
_⊇_ L₁ L₂ = ∀{x} → (x ∈ L₁) ← (x ∈ L₂)

_≡_ : List{ℓ₂}(T) → List{ℓ₂}(T) → Stmt
_≡_ L₁ L₂ = ∀{x} → (x ∈ L₁) ↔ (x ∈ L₂)

_⊈_ : List{ℓ₂}(T) → List{ℓ₂}(T) → Stmt
_⊈_ L₁ L₂ = ¬(L₁ ⊆ L₂)

_⊉_ : List{ℓ₂}(T) → List{ℓ₂}(T) → Stmt
_⊉_ L₁ L₂ = ¬(L₁ ⊇ L₂)

_≢_ : List{ℓ₂}(T) → List{ℓ₂}(T) → Stmt
_≢_ L₁ L₂ = ¬(L₁ ≡ L₂)
