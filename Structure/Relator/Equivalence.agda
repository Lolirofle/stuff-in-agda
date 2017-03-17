module Structure.Relator.Equivalence lvl where

open import Logic(lvl)
open import Structure.Relator.Properties(lvl)

record Equivalence {T : Set} (_≡_ : T → T → Stmt) : Stmt where
  field
    reflexivity  : Reflexivity  (_≡_)
    symmetry     : Symmetry     (_≡_)
    transitivity : Transitivity (_≡_)
