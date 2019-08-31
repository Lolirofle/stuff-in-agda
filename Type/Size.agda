module Type.Size where

import      Lvl
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Function.Domain
open import Type

_≍_ : ∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Stmt
_≍_ A B = ∃{Object = A → B}(Bijective)

_≼_ : ∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Stmt
_≼_ A B = ∃{Object = A → B}(Injective)

_≽_ : ∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Stmt
_≽_ A B = ∃{Object = A → B}(Surjective)

_≭_ : ∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Stmt
_≭_ A B = ¬(A ≍ B)

_≺_ : ∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Stmt
_≺_ A B = (A ≼ B) ∧ (A ≭ B)

_≻_ : ∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Stmt
_≻_ A B = (A ≽ B) ∧ (A ≭ B)
