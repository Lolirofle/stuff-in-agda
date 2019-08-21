module Cardinal.Proofs{ℓₗ}{ℓₒ} where

import      Lvl
open import Cardinal{ℓₗ}{ℓₒ}
open import Functional
open import Functional.Proofs
open import Logic.Propositional{ℓₗ Lvl.⊔ (Lvl.𝐒(ℓₒ))}
open import Logic.Predicate
open import Relator.Equals
open import Structure.Function.Domain
open import Structure.Relator.Equivalence
open import Structure.Relator.Ordering
open import Structure.Relator.Properties{ℓₗ Lvl.⊔ (Lvl.𝐒(ℓₒ))}
open import Type

[≍]-reflexivity : Reflexivity(_≍_)
reflexivity ⦃ [≍]-reflexivity ⦄ = [∃]-intro(id)
