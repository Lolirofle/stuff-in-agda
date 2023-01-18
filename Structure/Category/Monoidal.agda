module Structure.Category.Monoidal where

import      Lvl
open import Data.Tuple as Tuple using (_,_ ; _⨯_)
open import Data.Tuple.Category
open import Data.Tuple.Equivalence
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Category
open import Structure.Category.Functor
import      Structure.Category.Functor.Functors as Functors
open import Structure.Category.NaturalIsomorphism
open import Structure.Category.NaturalTransformation
open import Type

private variable ℓ ℓₒ ℓₘ ℓₑ ℓₒ₁ ℓₘ₁ ℓₑ₁ ℓₒ₂ ℓₘ₂ ℓₑ₂ : Lvl.Level
private variable Obj : Type{ℓ}
private variable Morphism : Obj → Obj → Type{ℓ}

open Functors.Wrapped

module _
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}}
  (⊗ᶠᵘⁿᶜᵗᵒʳ : (C ⨯ᶜᵃᵗ C) →ᶠᵘⁿᶜᵗᵒʳ C)
  (𝟏 : CategoryObject.Object(C))
  where

  open CategoryObject(C)
  open Category.ArrowNotation(category)
  open Functor

  record MonoidalCategory : Type{Lvl.of(Type.of C)} where
    constructor intro
    field
      associator : (((⊗ᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ (Tupleᶜᵃᵗ.mapLeft ⊗ᶠᵘⁿᶜᵗᵒʳ))) ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.associateLeft) ↔ᴺᵀ (⊗ᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ (Tupleᶜᵃᵗ.mapRight ⊗ᶠᵘⁿᶜᵗᵒʳ))
      unitorₗ : (⊗ᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.constₗ 𝟏) ↔ᴺᵀ idᶠᵘⁿᶜᵗᵒʳ
      unitorᵣ : (⊗ᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.constᵣ 𝟏) ↔ᴺᵀ idᶠᵘⁿᶜᵗᵒʳ

    _⊗_ : Object → Object → Object
    _⊗_ = Tuple.curry([∃]-witness ⊗ᶠᵘⁿᶜᵗᵒʳ)

    _<⊗>_ : ∀{x₁ x₂ y₁ y₂} → (x₁ ⟶ x₂) → (y₁ ⟶ y₂) → ((x₁ ⊗ y₁) ⟶ (x₂ ⊗ y₂))
    _<⊗>_ {x₁}{x₂}{y₁}{y₂} = Tuple.curry(map([∃]-proof ⊗ᶠᵘⁿᶜᵗᵒʳ) {x₁ , y₁}{x₂ , y₂})

    α : ∀(x)(y)(z) → (((x ⊗ y) ⊗ z) ⟶ (x ⊗ (y ⊗ z)))
    α x y z = [∃]-witness($ᵣᴺᵀ associator) (x , (y , z))

    υₗ : ∀(x) → ((𝟏 ⊗ x) ⟶ x)
    υₗ = [∃]-witness($ᵣᴺᵀ unitorₗ)

    υᵣ : ∀(x) → ((x ⊗ 𝟏) ⟶ x)
    υᵣ = [∃]-witness($ᵣᴺᵀ unitorᵣ)

    α⁻¹ : ∀(x)(y)(z) → ((x ⊗ (y ⊗ z)) ⟶ ((x ⊗ y) ⊗ z))
    α⁻¹ x y z = [∃]-witness($ₗᴺᵀ associator) (x , (y , z))

    υₗ⁻¹ : ∀(x) → (x ⟶ (𝟏 ⊗ x))
    υₗ⁻¹ = [∃]-witness ($ₗᴺᵀ unitorₗ)

    υᵣ⁻¹ : ∀(x) → (x ⟶ (x ⊗ 𝟏))
    υᵣ⁻¹ = [∃]-witness ($ₗᴺᵀ unitorᵣ)

    -- Coherence conditions.
    field
      associativity-condition : ∀{x y z w} → ((id{x} <⊗> α(y)(z)(w)) ∘ α(x)(y ⊗ z)(w) ∘ (α(x)(y)(z) <⊗> id{w}) ≡ α(x)(y)(z ⊗ w) ∘ α(x ⊗ y)(z)(w))
      unitality-condition : ∀{x y} → ((id{x} <⊗> υₗ(y)) ∘ α(x)(𝟏)(y) ≡ υᵣ(x) <⊗> id{y})

    α-natural : ∀{(x₁ , (x₂ , x₃)) (y₁ , (y₂ , y₃)) : Object ⨯ (Object ⨯ Object)}
                 {(f₁ , f₂ , f₃) : ((x₁ ⟶ y₁) ⨯ ((x₂ ⟶ y₂) ⨯ (x₃ ⟶ y₃)))} →
                 ((α y₁ y₂ y₃) ∘ ((f₁ <⊗> f₂) <⊗> f₃) ≡ (f₁ <⊗> (f₂ <⊗> f₃)) ∘ (α x₁ x₂ x₃))
    α-natural = NaturalTransformation.natural(NaturalIsomorphism.naturalTransformationᵣ([∃]-proof associator))

    υₗ-natural : ∀{x y}{f : x ⟶ y} → (υₗ(y) ∘ (id <⊗> f) ≡ f ∘ υₗ(x))
    υₗ-natural = NaturalTransformation.natural(NaturalIsomorphism.naturalTransformationᵣ([∃]-proof unitorₗ))

    υᵣ-natural : ∀{x y}{f : x ⟶ y} → (υᵣ(y) ∘ (f <⊗> id) ≡ f ∘ υᵣ(x))
    υᵣ-natural = NaturalTransformation.natural(NaturalIsomorphism.naturalTransformationᵣ([∃]-proof unitorᵣ))

    α⁻¹-natural : ∀{((x₁ , x₂) , x₃) ((y₁ , y₂) , y₃) : (Object ⨯ Object) ⨯ Object}
                   {(f₁ , f₂ , f₃) : ((x₁ ⟶ y₁) ⨯ ((x₂ ⟶ y₂) ⨯ (x₃ ⟶ y₃)))} →
                   ((α⁻¹ y₁ y₂ y₃) ∘ (f₁ <⊗> (f₂ <⊗> f₃)) ≡ ((f₁ <⊗> f₂) <⊗> f₃) ∘ (α⁻¹ x₁ x₂ x₃))
    α⁻¹-natural = NaturalTransformation.natural(NaturalIsomorphism.naturalTransformationₗ([∃]-proof associator))

    υₗ⁻¹-natural : ∀{x y}{f : x ⟶ y} → (υₗ⁻¹(y) ∘ f ≡ (id <⊗> f) ∘ υₗ⁻¹(x))
    υₗ⁻¹-natural = NaturalTransformation.natural(NaturalIsomorphism.naturalTransformationₗ([∃]-proof unitorₗ))

    υᵣ⁻¹-natural : ∀{x y}{f : x ⟶ y} → (υᵣ⁻¹(y) ∘ f ≡ (f <⊗> id) ∘ υᵣ⁻¹(x))
    υᵣ⁻¹-natural = NaturalTransformation.natural(NaturalIsomorphism.naturalTransformationₗ([∃]-proof unitorᵣ))

record Monoidalᶜᵃᵗ{ℓₒ}{ℓₘ}{ℓₑ} (C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}) : Type{Lvl.𝐒(ℓₒ Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    productFunctor : (C ⨯ᶜᵃᵗ C) →ᶠᵘⁿᶜᵗᵒʳ C
    unitObject : CategoryObject.Object(C)
    ⦃ monoidalCategory ⦄ : MonoidalCategory(productFunctor)(unitObject)
  open MonoidalCategory(monoidalCategory) public
