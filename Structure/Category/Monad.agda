open import Structure.Category

module Structure.Category.Monad
  {ℓₒ ℓₘ ℓₑ}
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}}
  where

import      Function.Equals
open        Function.Equals.Dependent
open import DependentFunctional using () renaming (_∘_ to _∘ᶠⁿ_)
open import Logic.Predicate
import      Lvl
open import Structure.Category.Functor
open import Structure.Category.Functor.Functors as Functors
open import Structure.Category.NaturalTransformation
open import Structure.Category.NaturalTransformation.NaturalTransformations as NaturalTransformations
open import Structure.Setoid
open import Type

open CategoryObject(C)
open Category.ArrowNotation(category)
open Functors.Wrapped
open NaturalTransformations.Raw(C)(C)

-- A monad is a generalization of a binary operator with identity. In this special case, η is the identity element, μ is the operator, and the category is the monoid category of the monoid (_⨯_) on types.
record Monad(Tᶠᵘⁿᶜᵗᵒʳ : C →ᶠᵘⁿᶜᵗᵒʳ C) : Type{Lvl.of(Type.of(C))} where
  field
    Η : (idᶠᵘⁿᶜᵗᵒʳ →ᴺᵀ Tᶠᵘⁿᶜᵗᵒʳ)
    Μ : ((Tᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ Tᶠᵘⁿᶜᵗᵒʳ) →ᴺᵀ Tᶠᵘⁿᶜᵗᵒʳ)

  private
    T       = [∃]-witness Tᶠᵘⁿᶜᵗᵒʳ
    functor = [∃]-proof   Tᶠᵘⁿᶜᵗᵒʳ
  open Functor(functor)

  η : ∀(x) → (x ⟶ T(x))
  η = [∃]-witness Η

  μ : ∀(x) → (T(T(x)) ⟶ T(x))
  μ = [∃]-witness Μ

  η-natural : ∀{x y}{f} → (η(y) ∘ f ≡ map f ∘ η(x))
  η-natural = NaturalTransformation.natural([∃]-proof Η)

  μ-natural : ∀{x y}{f} → (μ(y) ∘ map(map f) ≡ map f ∘ μ(x))
  μ-natural = NaturalTransformation.natural([∃]-proof Μ)

  field
    μ-on-μ-preserving-functor : (μ ∘ᴺᵀ (map ∘ᶠⁿ μ) ⊜ μ ∘ᴺᵀ (μ ∘ᶠⁿ T))
    μ-on-μ-functor-η-inverse₁ : (μ ∘ᴺᵀ (map ∘ᶠⁿ η) ⊜ idᴺᵀ)
    μ-on-μ-functor-η-inverse₀ : (μ ∘ᴺᵀ (η   ∘ᶠⁿ T) ⊜ idᴺᵀ)

  -- Extension operator
  -- Also called: _*
  -- Alternative implementation: (μ(_) ∘_) ∘ᶠⁿ map
  ext : ∀{x y} → (x ⟶ T(y)) → (T(x) ⟶ T(y))
  ext{x}{y} f = μ(y) ∘ map(f)

  module FunctionalNames where
    lift : ∀{x} → (x ⟶ T(x))
    lift{x} = [∃]-witness Η(x)

    flatten : ∀{x} → (T(T(x)) ⟶ T(x))
    flatten{x} = [∃]-witness Μ(x)

    flatMap : ∀{x y} → (x ⟶ T(y)) → (T(x) ⟶ T(y))
    flatMap = ext

  module HaskellNames where
    return = FunctionalNames.lift
    join   = FunctionalNames.flatten
    bind   = FunctionalNames.flatMap
