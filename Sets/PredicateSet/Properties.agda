module Sets.PredicateSet.Properties{ℓₗ}{ℓₒ} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ}
open import Logic.Predicate{ℓₗ}{ℓₒ}
open import Numeral.FiniteStrict
open import Numeral.Natural
import      Relator.Equals
open import Sets.PredicateSet
open import Structure.Function.Domain

Empty : ∀{T} → PredSet{ℓₗ}{ℓₒ}(T) → Stmt
Empty(S) = (∀{x} → (x ∉ S))

NonEmpty : ∀{T} → PredSet{ℓₗ}{ℓₒ}(T) → Stmt
NonEmpty(S) = ∃(x ↦ (x ∈ S))
