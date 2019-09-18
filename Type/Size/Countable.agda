module Type.Size.Countable where

import      Lvl
open import Functional
open import Logic
open import Numeral.Natural
open import Relator.Equals.Equivalence
open import Type
open import Type.Size

-- Definition of a countable type
Countable : ∀{ℓ} → Type{ℓ} → Stmt
Countable(T) = (ℕ ≽ T)
