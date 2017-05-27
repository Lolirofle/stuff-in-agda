module Numeral.Natural.Relation.Countable {lvl₁} {lvl₂} where

import Level as Lvl
open import Functional
open import Logic.Propositional{lvl₁ Lvl.⊔ lvl₂}
open import Logic.Predicate{lvl₁}{lvl₂}
open import Numeral.Natural
open import Structure.Function.Domain{lvl₁}
open import Type{lvl₂}

Countable : Type → Stmt
Countable T = (∃{T → ℕ}(f ↦ Injective(f)))
