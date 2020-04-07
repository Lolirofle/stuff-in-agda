open import Sets.Setoid
open import Structure.Category
open import Type

module Structure.Category.Monad
  {ℓₒ ℓₘ}
  {Obj : Type{ℓₒ}}
  {Morphism : Obj → Obj → Type{ℓₘ}}
  ⦃ morphism-equiv : ∀{x y : Obj} → Equiv(Morphism x y) ⦄
  {cat : Category(Morphism)}
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

open Category.ArrowNotation(cat)
open Category(cat)
open Functors.Raw
open NaturalTransformations.Raw(cat)(cat)
private instance _ = cat

record Monad (T : Obj → Obj) : Type{Lvl.of(type-of(cat))} where
  field
    ⦃ functor ⦄ : Functor(cat)(cat)(T)
  open Functor(functor)

  field
    Η : (idᶠᵘⁿᶜᵗᵒʳ →ᴺᵀ T)      ⦃ Functors.identity ⦄ 
    Μ : ((T ∘ᶠᵘⁿᶜᵗᵒʳ T) →ᴺᵀ T) ⦃ Functors.composition functor functor ⦄

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

  module FunctionalNames where
    lift : ∀{x} → (x ⟶ T(x))
    lift{x} = [∃]-witness Η(x)

    join : ∀{x} → (T(T(x)) ⟶ T(x))
    join{x} = [∃]-witness Μ(x)
