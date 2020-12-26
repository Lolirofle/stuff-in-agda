open import Structure.Setoid.WithLvl
open import Structure.Category
open import Type

module Structure.Category.Monad
  {ℓₒ ℓₘ ℓₑ}
  {cat : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}}
  where

import      Function.Equals
open        Function.Equals.Dependent
open import Functional.Dependent using () renaming (_∘_ to _∘ᶠⁿ_)
import      Lvl
open import Logic.Predicate
open import Structure.Category.Functor
open import Structure.Category.Functor.Functors as Functors
open import Structure.Category.NaturalTransformation
open import Structure.Category.NaturalTransformation.NaturalTransformations as NaturalTransformations

open CategoryObject(cat)
open Category.ArrowNotation(category)
open Category(category)
open Functors.Wrapped
open NaturalTransformations.Raw(intro category)(intro category)
private instance _ = cat

-- A monad is a generalization of a binary operator with identity. In this special case, η is the identity element, μ is the operator, and the category is the monoid category of the monoid (_⨯_) on types.
record Monad (T : Object → Object) ⦃ functor : Functor(category)(category)(T) ⦄ : Type{Lvl.of(Type.of(cat))} where
  open Functor(functor)

  functor-object : cat →ᶠᵘⁿᶜᵗᵒʳ cat
  functor-object = [∃]-intro T ⦃ functor ⦄
  private Tᶠᵘⁿᶜᵗᵒʳ = functor-object

  field
    Η : (idᶠᵘⁿᶜᵗᵒʳ →ᴺᵀ Tᶠᵘⁿᶜᵗᵒʳ)
    Μ : ((Tᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ Tᶠᵘⁿᶜᵗᵒʳ) →ᴺᵀ Tᶠᵘⁿᶜᵗᵒʳ)

  η = [∃]-witness Η
  μ = [∃]-witness Μ

  η-natural : ∀{x y}{f} → (η(y) ∘ f ≡ map f ∘ η(x))
  η-natural = NaturalTransformation.natural([∃]-proof Η)

  μ-natural : ∀{x y}{f} → (μ(y) ∘ map(map f) ≡ map f ∘ μ(x))
  μ-natural = NaturalTransformation.natural([∃]-proof Μ)

  field
    μ-functor-[∘]-commutativity : (μ ∘ᴺᵀ (map ∘ᶠⁿ μ) ⊜ μ ∘ᴺᵀ (μ ∘ᶠⁿ T))
    μ-functor-[∘]-identityₗ     : (μ ∘ᴺᵀ (map ∘ᶠⁿ η) ⊜ idᴺᵀ)
    μ-functor-[∘]-identityᵣ     : (μ ∘ᴺᵀ (η   ∘ᶠⁿ T) ⊜ idᴺᵀ)

  -- Extension operator
  -- Also called: _*
  -- Alternative implementation: (μ(_) ∘_) ∘ᶠⁿ map
  ext : ∀{x y} → (x ⟶ T(y)) → (T(x) ⟶ T(y))
  ext {x}{y} f = μ(y) ∘ map(f)

  module FunctionalNames where
    lift : ∀{x} → (x ⟶ T(x))
    lift{x} = [∃]-witness Η(x)

    join : ∀{x} → (T(T(x)) ⟶ T(x))
    join{x} = [∃]-witness Μ(x)
