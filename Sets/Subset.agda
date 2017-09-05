module Sets.Subset {ℓ₁} {ℓ₂} where

import      Level as Lvl
open import Data
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}

-- An element in Subset(S) is in the subset of S.
-- Something of type Subset(S) is of a restricted part of S.
record Subset {S : Set(ℓ₂)} (P : S → Stmt) : Set(ℓ₁ Lvl.⊔ ℓ₂) where
  constructor subelem
  field
    elem             : S
    ⦃ satisfaction ⦄ : P(elem)
