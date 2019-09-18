module Type.Size.Finite where

import      Lvl
open import Functional
open import Logic
open import Logic.Predicate
open import Numeral.Finite
open import Relator.Equals.Equivalence
open import Type
open import Type.Size

-- Definition of a finite type
Finite : ∀{ℓ} → Type{ℓ} → Stmt
Finite(T) = ∃(n ↦ T ≍ 𝕟(n))
