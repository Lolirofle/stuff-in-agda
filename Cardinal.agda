module Cardinal {ℓₗ} {ℓₒ} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓₗ Lvl.⊔ (Lvl.𝐒(ℓₒ))}
open import Logic.Predicate{ℓₗ}{Lvl.𝐒(ℓₒ)}
open import Relator.Equals{ℓₗ}{Lvl.𝐒(ℓₒ)}
open import Structure.Function.Domain{ℓₗ}
open import Structure.Relator.Equivalence{ℓₗ}{Lvl.𝐒(ℓₒ)}
open import Structure.Relator.Ordering{ℓₗ}{Lvl.𝐒(ℓₒ)}
open import Structure.Relator.Properties{ℓₗ}{Lvl.𝐒(ℓₒ)}
open import Type{ℓₒ}

_≍_ : Type → Type → Stmt
_≍_ A B = ∃{A → B}(Bijective)

_≼_ : Type → Type → Stmt
_≼_ A B = ∃{A → B}(Injective)

_≽_ : Type → Type → Stmt
_≽_ A B = _≼_ B A

_≺_ : Type → Type → Stmt
_≺_ A B = (A ≼ B) ∧ ¬(A ≍ B)

_≻_ : Type → Type → Stmt
_≻_ A B = (A ≽ B) ∧ ¬(A ≍ B)

postulate [≍]-reflexivity : Reflexivity(_≍_)
-- reflexivity ⦃ [≍]-reflexivity ⦄
