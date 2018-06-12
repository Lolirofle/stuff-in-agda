module Relator.Finite {ℓ₁} where

import      Lvl
open import Functional
open import Functional.Proofs
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.FiniteStrict
open import Numeral.Natural
open import Structure.Function.Domain{ℓ₁}
open import Structure.Relator.Properties {ℓ₁}
open import Type

-- Definition of a finite set/type
Finite : ∀{ℓ₂} → Type{ℓ₂} → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
Finite {ℓ₂} (T) = ∃{ℓ₁ Lvl.⊔ ℓ₂}{Lvl.𝟎}{ℕ}(n ↦ (∃{ℓ₁}{ℓ₂}{T → 𝕟(n)} Injective))
-- TODO: Create a module Relator.Injection like Relator.Bijection
