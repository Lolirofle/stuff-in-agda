module Structure.Operator.Vector {ℓ₁} {ℓ₂} where

import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂}{ℓ₂}
open import Relator.Equals.Theorems{ℓ₁}{ℓ₂}
open import Structure.Operator.Field{ℓ₁}{ℓ₂}
open import Structure.Operator.Group{ℓ₁}{ℓ₂}
open import Structure.Operator.Monoid{ℓ₁}{ℓ₂}
open import Structure.Operator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

record Language (V S : Type) : Stmt where
  field
    _+ᵥ_ : V → V → V
    _⋅ₛᵥ_ : S → V → V
    _+ₛ_ : S → S → S
    _⋅ₛ_ : S → S → S

record VectorSpace (V S : Type) ⦃ lang : Language(V)(S) ⦄ : Stmt where
  open Language(lang)

  field
   ⦃ scalarField ⦄       : Field(_+ₛ_)(_⋅ₛ_)
   ⦃ vectorAbelianGroup ⦄ : AbelianGroup(_+ᵥ_)

  open AbelianGroup ⦃ ... ⦄ 
  open Field ⦃ ... ⦄ 
  open Group ⦃ ... ⦄ 
  open Monoid ⦃ ... ⦄ 
  open MultGroup ⦃ ... ⦄ 

  -- Scalar zero
  𝟎ₛ : S
  𝟎ₛ = id ⦃ Group.monoid ([+]-group ⦃ scalarField ⦄) ⦄

  -- Scalar one
  𝟏ₛ : S
  𝟏ₛ = id ⦃ MultGroup.monoid ([⋅]-group ⦃ scalarField ⦄) ⦄

  [⋅ₛᵥ]-id = 𝟏ₛ

  -- Scalar negation
  −₁ₛ_ : S → S
  −₁ₛ_ = Group.inv ([+]-group ⦃ scalarField ⦄)

  -- Scalar subtraction
  _−ₛ_ : S → S → S
  _−ₛ_ (a)(b) = a +ₛ (−₁ₛ_ b)

  -- Scalar reciprocal
  ⅟ₛ_ : (x : S) → ⦃ _ : (x ≢ 𝟎ₛ) ⦄ → S
  ⅟ₛ_ = MultGroup.inv ([⋅]-group ⦃ scalarField ⦄)

  -- Scalar division
  _/ₛ_ : S → (b : S) → ⦃ _ : (b ≢ 𝟎ₛ) ⦄ → S
  _/ₛ_ (a)(b) ⦃ nonzero ⦄ = a ⋅ₛ (⅟ₛ_ b ⦃ nonzero ⦄)

  -- Vector zero
  𝟎ᵥ : V
  𝟎ᵥ = id ⦃ Group.monoid(group ⦃ vectorAbelianGroup ⦄) ⦄

  -- Vector negation
  −₁ᵥ_ : V → V
  −₁ᵥ_ = Group.inv(group ⦃ vectorAbelianGroup ⦄)

  -- Vector subtraction
  _−ᵥ_ : V → V → V
  _−ᵥ_ (a)(b) = a +ᵥ (−₁ᵥ_ b)

  field
    [⋅ₛ][⋅ₛᵥ]-compatibility      : Compatibility(_⋅ₛ_)(_⋅ₛᵥ_)
    [⋅ₛᵥ]-identity               : Identityₗ(_⋅ₛᵥ_)([⋅ₛᵥ]-id)
    [⋅ₛᵥ][+ᵥ]-distributivity     : Distributivityₗ(_⋅ₛᵥ_)(_+ᵥ_)
    [⋅ₛᵥ][+ₛ][+ᵥ]-distributivity : DistributivityPatternᵣ(_⋅ₛᵥ_)(_+ₛ_)(_+ᵥ_)

  module Theorems where
    postulate [⋅ₛᵥ]-absorberₗ : ∀{v} → (𝟎ₛ ⋅ₛᵥ v ≡ 𝟎ᵥ)
    postulate [⋅ₛᵥ]-absorberᵣ : ∀{s} → (s ⋅ₛᵥ 𝟎ᵥ ≡ 𝟎ᵥ)
    postulate [⋅ₛᵥ]-negation : ∀{v} → ((−₁ₛ 𝟏ₛ) ⋅ₛᵥ v ≡ −₁ᵥ v)
