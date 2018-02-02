module Cardinal {ℓₗ} {ℓₒ} where

import      Lvl
open import Functional
open import Functional.Properties
open import Logic.Propositional{ℓₗ Lvl.⊔ (Lvl.𝐒(ℓₒ))}
open import Logic.Predicate
open import Relator.Equals
open import Structure.Function.Domain
open import Structure.Relator.Equivalence
open import Structure.Relator.Ordering
open import Structure.Relator.Properties{ℓₗ Lvl.⊔ (Lvl.𝐒(ℓₒ))}
open import Type

_≍_ : Type{ℓₒ} → Type{ℓₒ} → Stmt
_≍_ A B = ∃{_}{_}{A → B}(Bijective)

_≼_ : Type{ℓₒ} → Type{ℓₒ} → Stmt
_≼_ A B = ∃{_}{_}{A → B}(Injective)

_≽_ : Type → Type → Stmt
_≽_ A B = _≼_ B A

_≭_ : Type → Type → Stmt
_≭_ A B = ¬(A ≍ B)

_≺_ : Type → Type → Stmt
_≺_ A B = (A ≼ B) ∧ (A ≭ B)

_≻_ : Type → Type → Stmt
_≻_ A B = (A ≽ B) ∧ (A ≭ B)

[≍]-reflexivity : Reflexivity(_≍_)
reflexivity ⦃ [≍]-reflexivity ⦄ = [∃]-intro(id)
