module Structure.Relator.Equivalence {ℓ₁} {ℓ₂} where

import      Level as Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Structure.Relator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

-- Definition of an equivalence class
record Equivalence {T : Type} (_≡_ : T → T → Stmt) : Stmt where
  field
    reflexivity  : Reflexivity  (_≡_)
    symmetry     : Symmetry     (_≡_)
    transitivity : Transitivity (_≡_)
