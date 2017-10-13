module Sets.Subset {ℓ₁} {ℓ₂} where

import      Lvl
open import Data
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

-- An element in Subset(S) is in the subset of S.
-- Something of type Subset(S) is of a restricted part of S.
record Subset {S : Type} (P : S → Stmt) : Stmt where -- TODO: Cannot be Type?
  constructor subelem
  field
    elem             : S
    ⦃ satisfaction ⦄ : P(elem)
