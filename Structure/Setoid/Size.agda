module Structure.Setoid.Size where

import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid.WithLvl
open import Structure.Function.Domain
open import Structure.Function
open import Syntax.Function
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂ : Lvl.Level

_≍_ : (A : Setoid{ℓₑ₁}{ℓ₁}) → (B : Setoid{ℓₑ₂}{ℓ₂}) → Stmt
_≍_ A B = ∃{Obj = Setoid.Type(A) → Setoid.Type(B)} (f ↦ Function(f) ∧ Bijective(f))

_≼_ : (A : Setoid{ℓₑ₁}{ℓ₁}) → (B : Setoid{ℓₑ₂}{ℓ₂}) → Stmt
_≼_ A B = ∃{Obj = Setoid.Type(A) → Setoid.Type(B)} (f ↦ Function(f) ∧ Injective(f))

_≽_ : (A : Setoid{ℓₑ₁}{ℓ₁}) → (B : Setoid{ℓₑ₂}{ℓ₂}) → Stmt
_≽_ A B = ∃{Obj = Setoid.Type(A) → Setoid.Type(B)} (f ↦ Function(f) ∧ Surjective(f))

_≭_ : (A : Setoid{ℓₑ₁}{ℓ₁}) → (B : Setoid{ℓₑ₂}{ℓ₂}) → Stmt
_≭_ A B = ¬(A ≍ B)

_≺_ : (A : Setoid{ℓₑ₁}{ℓ₁}) → (B : Setoid{ℓₑ₂}{ℓ₂}) → Stmt
_≺_ A B = (A ≼ B) ∧ (A ≭ B)

_≻_ : (A : Setoid{ℓₑ₁}{ℓ₁}) → (B : Setoid{ℓₑ₂}{ℓ₂}) → Stmt
_≻_ A B = (A ≽ B) ∧ (A ≭ B)
