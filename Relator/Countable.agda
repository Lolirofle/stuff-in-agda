module Relator.Countable {ℓ₁} {ℓ₂} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Numeral.Natural
open import Structure.Function.Domain{ℓ₁ Lvl.⊔ ℓ₂}
open import Type{ℓ₂}

-- Definition of a finite set/type
Countable : Type → Stmt
Countable (T) = ∃{T → ℕ} Injective
-- TODO: Create a module Relator.Injection like Relator.Bijection
