module Structure.Operator.Field {ℓ₁} {ℓ₂} where

import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Sets.Setoid{ℓ₁}
open import Structure.Operator.Group{ℓ₁}{ℓ₂}
open import Structure.Operator.Monoid{ℓ₁}{ℓ₂}
open import Structure.Operator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}
open import Sets.PredicateSet.Filter{ℓ₁}{ℓ₂}

record Field {T : Type} ⦃ _ : Equiv(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt where
  open Monoid ⦃ ... ⦄

  field
    instance ⦃ [+]-group ⦄ : Group (_+_)
    instance ⦃ [⋅]-group ⦄ : MultGroup (_⋅_) (id ⦃ _ ⦄ ⦃ Group.monoid([+]-group) ⦄)
    [⋅][+]-distributivityₗ : Distributivityₗ (_⋅_) (_+_)
    [⋅][+]-distributivityᵣ : Distributivityᵣ (_⋅_) (_+_)
