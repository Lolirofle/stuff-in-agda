open import Structure.Setoid.WithLvl
open import Structure.Category
open import Type

module Structure.Category.CoMonad
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

record CoMonad (T : Object → Object) ⦃ functor : Functor(category)(category)(T) ⦄ : Type{Lvl.of(Type.of(cat))} where
  open Functor(functor)

  functor-object : cat →ᶠᵘⁿᶜᵗᵒʳ cat
  functor-object = [∃]-intro T ⦃ functor ⦄
  private Tᶠᵘⁿᶜᵗᵒʳ = functor-object

  field
    Η : (Tᶠᵘⁿᶜᵗᵒʳ →ᴺᵀ idᶠᵘⁿᶜᵗᵒʳ)
    Μ : (Tᶠᵘⁿᶜᵗᵒʳ →ᴺᵀ (Tᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ Tᶠᵘⁿᶜᵗᵒʳ))

  η = [∃]-witness Η
  μ = [∃]-witness Μ

  η-natural : ∀{x y}{f} → (η(y) ∘ map f ≡ f ∘ η(x))
  η-natural = NaturalTransformation.natural([∃]-proof Η)

  μ-natural : ∀{x y}{f} → (μ(y) ∘ map f ≡ map(map f) ∘ μ(x))
  μ-natural = NaturalTransformation.natural([∃]-proof Μ)

  field
    μ-functor-[∘]-commutativity : ((μ ∘ᶠⁿ T) ∘ᴺᵀ μ ⊜ (map ∘ᶠⁿ μ) ∘ᴺᵀ μ)
    μ-functor-[∘]-identityₗ     : ((map ∘ᶠⁿ η) ∘ᴺᵀ μ ⊜ idᴺᵀ)
    μ-functor-[∘]-identityᵣ     : ((η   ∘ᶠⁿ T) ∘ᴺᵀ μ ⊜ idᴺᵀ)

  module FunctionalNames where
    extract : ∀{x} → (T(x) ⟶ x)
    extract{x} = [∃]-witness Η(x)

    duplicate : ∀{x} → (T(x) ⟶ T(T(x)))
    duplicate{x} = [∃]-witness Μ(x)
