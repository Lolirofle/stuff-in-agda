module Structure.Operator.Vector where

import      Lvl
open import Logic
open import Logic.Propositional
open import Sets.Setoid
open import Structure.Operator.Field
open import Structure.Operator.Group
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Type

record VectorSpace {ℓᵥ ℓₛ}
                   {V : Type{ℓᵥ}} ⦃ _ : Equiv(V) ⦄
                   {S : Type{ℓₛ}} ⦃ _ : Equiv(S) ⦄
                   (_+ᵥ_ : V → V → V)
                   (_⋅ₛᵥ_ : S → V → V)
                   (_+ₛ_ : S → S → S)
                   (_⋅ₛ_ : S → S → S)
                   : Stmt where
  constructor intro
  field
    ⦃ scalarField ⦄            : Field(_+ₛ_)(_⋅ₛ_)
    ⦃ vectorCommutativeGroup ⦄ : CommutativeGroup(_+ᵥ_)

  {-
  open Field ⦃ ... ⦄
  open Group ⦃ ... ⦄

  -- Scalar zero
  𝟎ₛ : S
  𝟎ₛ = id ⦃ _ ⦄ ⦃ Field.[⋅]-monoid ⦄

  -- Scalar one
  𝟏ₛ : S
  𝟏ₛ = id ⦃ _ ⦄ ⦃ Field.[⋅]-monoid ⦄

  [⋅ₛᵥ]-id = 𝟏ₛ

  -- Scalar negation
  −₁ₛ_ : S → S
  −₁ₛ_ = Group.inv ([+]-group ⦃ _ ⦄ ⦃ scalarField ⦄)

  -- Scalar subtraction
  _−ₛ_ : S → S → S
  _−ₛ_ (a)(b) = a +ₛ (−₁ₛ_ b)

  -- Scalar reciprocal
  ⅟ₛ_ : (x : S) → ⦃ _ : (x ≢ 𝟎ₛ) ⦄ → S
  ⅟ₛ_ = MultGroup.inv ([⋅]-group ⦃ _ ⦄ ⦃ scalarField ⦄)

  -- Scalar division
  _/ₛ_ : S → (b : S) → ⦃ _ : (b ≢ 𝟎ₛ) ⦄ → S
  _/ₛ_ (a)(b) ⦃ nonzero ⦄ = a ⋅ₛ (⅟ₛ_ b ⦃ nonzero ⦄)

  -- Vector zero
  𝟎ᵥ : V
  𝟎ᵥ = id ⦃ _ ⦄ ⦃ Group.monoid(group ⦃ _ ⦄ ⦃ vectorCommutativeGroup ⦄) ⦄

  -- Vector negation
  −₁ᵥ_ : V → V
  −₁ᵥ_ = Group.inv(group ⦃ _ ⦄ ⦃ vectorCommutativeGroup ⦄)

  -- Vector subtraction
  _−ᵥ_ : V → V → V
  _−ᵥ_ (a)(b) = a +ᵥ (−₁ᵥ_ b)
  -}

  field
    [⋅ₛ][⋅ₛᵥ]-compatibility      : Compatibility(_⋅ₛ_)(_⋅ₛᵥ_)
    [⋅ₛᵥ]-identity               : Identityₗ(_⋅ₛᵥ_)([⋅ₛᵥ]-id)
    [⋅ₛᵥ][+ᵥ]-distributivity     : Distributivityₗ(_⋅ₛᵥ_)(_+ᵥ_)
    [⋅ₛᵥ][+ₛ][+ᵥ]-distributivity : DistributivityPatternᵣ(_⋅ₛᵥ_)(_+ₛ_)(_+ᵥ_) -- TODO: This is ∀? → Preserving₂
  {-
  module Theorems where
    postulate [⋅ₛᵥ]-absorberₗ : ∀{v} → (𝟎ₛ ⋅ₛᵥ v ≡ 𝟎ᵥ)
    postulate [⋅ₛᵥ]-absorberᵣ : ∀{s} → (s ⋅ₛᵥ 𝟎ᵥ ≡ 𝟎ᵥ)
    postulate [⋅ₛᵥ]-negation : ∀{v} → ((−₁ₛ 𝟏ₛ) ⋅ₛᵥ v ≡ −₁ᵥ v)
  -}
