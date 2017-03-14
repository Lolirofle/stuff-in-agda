module Structure.Relator.Equivalence where

open import Structure.Relator.Properties

record Equivalence {T : Set} (_≡_ : T → T → Set) : Set where
  field
    reflexivity  : Reflexivity  (_≡_)
    symmetry     : Symmetry     (_≡_)
    transitivity : Transitivity (_≡_)
