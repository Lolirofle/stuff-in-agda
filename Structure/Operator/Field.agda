module Structure.Operator.Field {ℓ₁} {ℓ₂} where

import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Relator.Equals.Theorems{ℓ₁}{ℓ₂}
open import Structure.Operator.Group{ℓ₁}{ℓ₂}
open import Structure.Operator.Monoid{ℓ₁}{ℓ₂}
open import Structure.Operator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}
open import Sets.Subset{ℓ₁}{ℓ₂}

record Field {T : Type} (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt where
  open Monoid {{...}}

  field
    ⦃ [+]-group ⦄ : Group (_+_)
    ⦃ [⋅]-group ⦄ : MultGroup (_⋅_) (id ⦃ Group.monoid([+]-group) ⦄)
    [⋅][+]-distributivityₗ : Distributivityₗ (_⋅_) (_+_)
    [⋅][+]-distributivityᵣ : Distributivityᵣ (_⋅_) (_+_)
