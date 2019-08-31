module Sets.PredicateSet.Finite{ℓₗ}{ℓₒ} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ}
open import Logic.Predicate{ℓₗ}{ℓₒ}
open import Numeral.Finite
open import Numeral.Natural
import      Relator.Equals
open import Sets.PredicateSet
open import Structure.Function.Domain
open import Type{ℓₒ}

{-
record Irrelevant∃ {X : Type} (Pred : X → Stmt) : Stmt where
  field
    witness   : X
    ⦃ .proof ⦄ : Pred(witness)

record Finite {T} (S : PredSet{ℓₗ}{ℓₒ}(T)) : Stmt where
  field
    count     : ℕ
    bijection : 𝕟(count) → Irrelevant∃(x ↦ (x ∈ S))
    proof     : Bijective(bijection) -- TODO: Bijective must allow different levels
-}
