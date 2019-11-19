module Sets.Setoid.Size where

import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid hiding (Function)
open import Structure.Function.Domain
open import Syntax.Function
open import Type

_≍_ : ∀{ℓ₁ ℓ₂} → (A : Setoid{ℓ₁}) → (B : Setoid{ℓ₂}) → Stmt
_≍_ A B = ∃{Obj = Setoid.Type(A) → Setoid.Type(B)} (f ↦ Function(f) ∧ Bijective(f))

_≼_ : ∀{ℓ₁ ℓ₂} → (A : Setoid{ℓ₁}) → (B : Setoid{ℓ₂}) → Stmt
_≼_ A B = ∃{Obj = Setoid.Type(A) → Setoid.Type(B)} (f ↦ Function(f) ∧ Injective(f))

_≽_ : ∀{ℓ₁ ℓ₂} → (A : Setoid{ℓ₁}) → (B : Setoid{ℓ₂}) → Stmt
_≽_ A B = ∃{Obj = Setoid.Type(A) → Setoid.Type(B)} (f ↦ Function(f) ∧ Surjective(f))

_≭_ : ∀{ℓ₁ ℓ₂} → (A : Setoid{ℓ₁}) → (B : Setoid{ℓ₂}) → Stmt
_≭_ A B = ¬(A ≍ B)

_≺_ : ∀{ℓ₁ ℓ₂} → (A : Setoid{ℓ₁}) → (B : Setoid{ℓ₂}) → Stmt
_≺_ A B = (A ≼ B) ∧ (A ≭ B)

_≻_ : ∀{ℓ₁ ℓ₂} → (A : Setoid{ℓ₁}) → (B : Setoid{ℓ₂}) → Stmt
_≻_ A B = (A ≽ B) ∧ (A ≭ B)