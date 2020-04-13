module Type.Size where

import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Function.Domain
open import Type

_≍_ : ∀{ℓ₁ ℓ₂} → (A : Type{ℓ₁}) → ⦃ _ : Equiv(A) ⦄ → (B : Type{ℓ₂}) → ⦃ _ : Equiv(B) ⦄ → Stmt
_≍_ A B = ∃{Obj = A → B}(Bijective)

_≼_ : ∀{ℓ₁ ℓ₂} → (A : Type{ℓ₁}) → ⦃ _ : Equiv(A) ⦄ → (B : Type{ℓ₂}) → ⦃ _ : Equiv(B) ⦄ → Stmt
_≼_ A B = ∃{Obj = A → B}(Injective)

_≽_ : ∀{ℓ₁ ℓ₂} → (A : Type{ℓ₁}) → (B : Type{ℓ₂}) → ⦃ _ : Equiv(B) ⦄ → Stmt
_≽_ A B = ∃{Obj = A → B}(Surjective)

_≭_ : ∀{ℓ₁ ℓ₂} → (A : Type{ℓ₁}) → ⦃ _ : Equiv(A) ⦄ → (B : Type{ℓ₂}) → ⦃ _ : Equiv(B) ⦄ → Stmt
_≭_ A B = ¬(A ≍ B)

_≺_ : ∀{ℓ₁ ℓ₂} → (A : Type{ℓ₁}) → ⦃ _ : Equiv(A) ⦄ → (B : Type{ℓ₂}) → ⦃ _ : Equiv(B) ⦄ → Stmt
_≺_ A B = (A ≼ B) ∧ (A ≭ B)

_≻_ : ∀{ℓ₁ ℓ₂} → (A : Type{ℓ₁}) → ⦃ _ : Equiv(A) ⦄ → (B : Type{ℓ₂}) → ⦃ _ : Equiv(B) ⦄ → Stmt
_≻_ A B = (A ≽ B) ∧ (A ≭ B)
