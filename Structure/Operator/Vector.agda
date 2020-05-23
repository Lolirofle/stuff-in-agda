module Structure.Operator.Vector where

import      Lvl
open import Logic
open import Logic.Propositional
open import Structure.Setoid
open import Structure.Operator.Field
open import Structure.Operator.Group
open import Structure.Operator.Monoid
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Type

record VectorSpace {ℓᵥ ℓₛ}
                   {V : Type{ℓᵥ}} ⦃ _ : Equiv(V) ⦄
                   {S : Type{ℓₛ}} ⦃ _ : Equiv(S) ⦄
                   (_+ᵥ_ : V → V → V)
                   (_⋅ₛᵥ_ : S → V → V)
                   (_+ₛ_ : S → S → S)
                   (_⋅ₛ_ : S → S → S)
                   : Stmt{ℓᵥ Lvl.⊔ ℓₛ} where
  constructor intro
  field
    ⦃ scalarField ⦄            : Field(_+ₛ_)(_⋅ₛ_)
    ⦃ vectorCommutativeGroup ⦄ : CommutativeGroup(_+ᵥ_)

  open Field(scalarField) renaming (𝟎 to 𝟎ₛ ; 𝟏 to 𝟏ₛ ; _−_ to _−ₛ_ ; _/_ to _/ₛ_ ; −_ to −ₛ ; ⅟ to ⅟ₛ) public
  open CommutativeGroup(vectorCommutativeGroup) renaming (id to 𝟎ᵥ ; inv to −ᵥ_ ; inv-op to _−ᵥ_) public

  field
    [⋅ₛ][⋅ₛᵥ]-compatibility       : Names.Compatibility(_⋅ₛ_)(_⋅ₛᵥ_) -- TODO: This is semigroup action
    [⋅ₛᵥ]-identity                : Identityₗ(_⋅ₛᵥ_)(𝟏ₛ)
    [⋅ₛᵥ][+ᵥ]-distributivityₗ     : Distributivityₗ(_⋅ₛᵥ_)(_+ᵥ_)
    [⋅ₛᵥ][+ₛ][+ᵥ]-distributivityᵣ : Names.DistributivityPatternᵣ(_⋅ₛᵥ_)(_+ₛ_)(_+ᵥ_) -- TODO: This is ∀? → Preserving₂
