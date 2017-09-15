module Structure.Operator.Field {ℓ₁} {ℓ₂} where

import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Structure.Operator.Group{ℓ₁}{ℓ₂}
open import Structure.Operator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

record Field {T : Type} (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt where
  field
    [+]-group : Group (_+_)
    [⋅]-group : Group (_⋅_)
    [⋅][+]-distributivityₗ : Distributivityₗ (_⋅_) (_+_)
    [⋅][+]-distributivityᵣ : Distributivityᵣ (_⋅_) (_+_)
