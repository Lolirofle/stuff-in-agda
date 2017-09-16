module Structure.Operator.Vector {ℓ₁} {ℓ₂} where

import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Structure.Operator.Field{ℓ₁}{ℓ₂}
open import Structure.Operator.Group{ℓ₁}{ℓ₂}
open import Structure.Operator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

record VectorSpace (V S : Type) (_+ᵥ_ : V → V → V) (_⋅ₛᵥ_ : S → V → V) (_+ₛ_ : S → S → S) (_⋅ₛ_ : S → S → S) : Stmt where
  field
    {{scalarField}}        : Field(_+ₛ_)(_⋅ₛ_)
    {{vectorAbelianGroup}} : AbelianGroup(_+ᵥ_)

  open AbelianGroup {{...}}
  open Field {{...}}
  open Group {{...}}

  -- Scalar zero
  𝟎ₛ : S
  𝟎ₛ = id ⦃ [+]-group ⦃ scalarField ⦄ ⦄

  -- Scalar one
  𝟏ₛ : S
  𝟏ₛ = id ⦃ [⋅]-group ⦃ scalarField ⦄ ⦄

  [⋅ₛᵥ]-id = 𝟏ₛ

  -- Scalar negation
  −₁ₛ_ : S → S
  −₁ₛ_ = inv ⦃ [+]-group ⦃ scalarField ⦄ ⦄

  -- Scalar subtraction
  _−ₛ_ : S → S → S
  _−ₛ_ (a)(b) = a +ₛ (−₁ₛ_ b)

  -- Scalar reciprocal
  ⅟ₛ_ : S → S
  ⅟ₛ_ = inv ⦃ [⋅]-group ⦃ scalarField ⦄ ⦄

  -- Scalar division
  _/ₛ_ : S → S → S
  _/ₛ_ (a)(b) = a ⋅ₛ (⅟ₛ_ b)

  -- Vector zero
  𝟎ᵥ : V
  𝟎ᵥ = id ⦃ group ⦃ vectorAbelianGroup ⦄ ⦄

  -- Vector negation
  −₁ᵥ_ : V → V
  −₁ᵥ_ = inv ⦃ group ⦃ vectorAbelianGroup ⦄ ⦄

  -- Vector subtraction
  _−ᵥ_ : V → V → V
  _−ᵥ_ (a)(b) = a +ᵥ (−₁ᵥ_ b)

  field
    [⋅ₛ][⋅ₛᵥ]-compatibility      : Compatibility(_⋅ₛ_)(_⋅ₛᵥ_)
    [⋅ₛᵥ]-identity               : Identityₗ(_⋅ₛᵥ_)([⋅ₛᵥ]-id)
    [⋅ₛᵥ][+ᵥ]-distributivity     : Distributivityₗ(_⋅ₛᵥ_)(_+ᵥ_)
    [⋅ₛᵥ][+ₛ][+ᵥ]-distributivity : DistributivityPatternᵣ(_⋅ₛᵥ_)(_+ₛ_)(_+ᵥ_)

  module Theorems where
    postulate [⋅ₛᵥ]-absorber : ∀{v} → (𝟎ₛ ⋅ₛᵥ v ≡ 𝟎ᵥ)
    postulate [⋅ₛᵥ]-negation : ∀{v} → ((−₁ₛ 𝟏ₛ) ⋅ₛᵥ v ≡ −₁ᵥ v)
