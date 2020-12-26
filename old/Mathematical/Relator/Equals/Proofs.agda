module Relator.Equals.Proofs where

open import Relator.Equals
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid renaming (_≡_ to _≡ₛ_)

instance
  [≡]-reflexivity : ∀{ℓ}{A : Type{ℓ}} → Reflexivity(_≡_ {P = A})
  Reflexivity.proof([≡]-reflexivity) = constant-path

instance
  [≡]-symmetry : ∀{ℓ}{A : Type{ℓ}} → Symmetry(_≡_ {P = A})
  Symmetry.proof([≡]-symmetry) = reversed-path
