module Numeral.Natural.Relation.Countable {ℓ₁} {ℓ₂} where

import Level as Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Numeral.Natural
open import Structure.Function.Domain{ℓ₁}
open import Type{ℓ₂}

Countable : Type → Stmt
Countable(T) = (∃{T → ℕ}(f ↦ Injective(f)))
