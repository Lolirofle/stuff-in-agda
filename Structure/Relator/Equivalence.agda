module Structure.Relator.Equivalence {l₁} {l₂} where

import      Level as Lvl
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Structure.Relator.Properties{l₁}{l₂}
open import Type{l₁}

-- Definition of an equivalence class
record Equivalence {T : Type} (_≡_ : T → T → Stmt) : Stmt where
  field
    reflexivity  : Reflexivity  (_≡_)
    symmetry     : Symmetry     (_≡_)
    transitivity : Transitivity (_≡_)
