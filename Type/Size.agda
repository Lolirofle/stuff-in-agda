module Type.Size where

import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid.WithLvl
open import Structure.Function.Domain
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level

_≍_ : (A : Type{ℓ₁}) → ⦃ _ : Equiv{ℓₑ₁}(A) ⦄ → (B : Type{ℓ₂}) → ⦃ _ : Equiv{ℓₑ₂}(B) ⦄ → Stmt
A ≍ B = ∃{Obj = A → B}(Bijective)

_≼_ : (A : Type{ℓ₁}) → ⦃ _ : Equiv{ℓₑ₁}(A) ⦄ → (B : Type{ℓ₂}) → ⦃ _ : Equiv{ℓₑ₂}(B) ⦄ → Stmt
A ≼ B = ∃{Obj = A → B}(Injective)

_≽_ : (A : Type{ℓ₁}) → (B : Type{ℓ₂}) → ⦃ _ : Equiv{ℓₑ₂}(B) ⦄ → Stmt
A ≽ B = ∃{Obj = A → B}(Surjective)

_≭_ : (A : Type{ℓ₁}) → ⦃ _ : Equiv{ℓₑ₁}(A) ⦄ → (B : Type{ℓ₂}) → ⦃ _ : Equiv{ℓₑ₂}(B) ⦄ → Stmt
A ≭ B = ¬(A ≍ B)

_≺_ : (A : Type{ℓ₁}) → ⦃ _ : Equiv{ℓₑ₁}(A) ⦄ → (B : Type{ℓ₂}) → ⦃ _ : Equiv{ℓₑ₂}(B) ⦄ → Stmt
A ≺ B = (A ≼ B) ∧ (A ≭ B)

_≻_ : (A : Type{ℓ₁}) → ⦃ _ : Equiv{ℓₑ₁}(A) ⦄ → (B : Type{ℓ₂}) → ⦃ _ : Equiv{ℓₑ₂}(B) ⦄ → Stmt
A ≻ B = (A ≽ B) ∧ (A ≭ B)
