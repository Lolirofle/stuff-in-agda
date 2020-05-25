module Structure.Category.Monoidal where

import      Lvl
open import Data.Tuple as Tuple using (_,_ ; _⨯_)
open import Data.Tuple.Category
open import Data.Tuple.Equiv
import      Functional as Fn
open import Logic.Predicate
open import Structure.Setoid.WithLvl
open import Structure.Category
open import Structure.Category.Functor
import      Structure.Category.Functor.Functors as Functors
open import Structure.Category.NaturalTransformation
open import Syntax.Function
open import Type

private variable ℓ ℓₒ ℓₘ ℓₑ ℓₒ₁ ℓₘ₁ ℓₑ₁ ℓₒ₂ ℓₘ₂ ℓₑ₂ : Lvl.Level
private variable Obj : Type{ℓ}
private variable Morphism : Obj → Obj → Type{ℓ}

open Functors.Wrapped

module _
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}}
  (product@([∃]-intro _) : (C ⨯ᶜᵃᵗ C) →ᶠᵘⁿᶜᵗᵒʳ C)
  (𝟏 : CategoryObject.Object(C))
  where

  open CategoryObject(C)
  open Category.ArrowNotation(category)
  open Category(category)
  open Functor

  record MonoidalCategory : Type{Lvl.of(Type.of C)} where
    constructor intro

    field
      associator : (((product ∘ᶠᵘⁿᶜᵗᵒʳ (Tupleᶜᵃᵗ.mapLeft product))) ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.associateLeft) ↔ᴺᵀ (product ∘ᶠᵘⁿᶜᵗᵒʳ (Tupleᶜᵃᵗ.mapRight product))
      unitorₗ : (product ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.constₗ 𝟏) ↔ᴺᵀ idᶠᵘⁿᶜᵗᵒʳ
      unitorᵣ : (product ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.constᵣ 𝟏) ↔ᴺᵀ idᶠᵘⁿᶜᵗᵒʳ

    _⊗_ : Object → Object → Object
    _⊗_ = Tuple.curry([∃]-witness product)

    _<⊗>_ : ∀{x₁ x₂ y₁ y₂} → (x₁ ⟶ x₂) → (y₁ ⟶ y₂) → ((x₁ ⊗ y₁) ⟶ (x₂ ⊗ y₂))
    _<⊗>_ = Tuple.curry(map([∃]-proof product))

    α : ∀(x)(y)(z) → (((x ⊗ y) ⊗ z) ⟶ (x ⊗ (y ⊗ z)))
    α x y z = [∃]-witness associator (x , (y , z))

    υₗ : ∀(x) → ((𝟏 ⊗ x) ⟶ x)
    υₗ = [∃]-witness unitorₗ

    υᵣ : ∀(x) → ((x ⊗ 𝟏) ⟶ x)
    υᵣ = [∃]-witness unitorᵣ

    α⁻¹ : ∀(x)(y)(z) → ((x ⊗ (y ⊗ z)) ⟶ ((x ⊗ y) ⊗ z))
    α⁻¹ x y z = [∃]-witness (invᴺᵀ associator) (x , (y , z))

    υₗ⁻¹ : ∀(x) → (x ⟶ (𝟏 ⊗ x))
    υₗ⁻¹ = [∃]-witness (invᴺᵀ unitorₗ)

    υᵣ⁻¹ : ∀(x) → (x ⟶ (x ⊗ 𝟏))
    υᵣ⁻¹ = [∃]-witness (invᴺᵀ unitorᵣ)

    α-natural : ∀{(x₁ , (x₂ , x₃)) (y₁ , (y₂ , y₃)) : Object ⨯ (Object ⨯ Object)}
                 {(f₁ , f₂ , f₃) : ((x₁ ⟶ y₁) ⨯ ((x₂ ⟶ y₂) ⨯ (x₃ ⟶ y₃)))} →
                 ((α y₁ y₂ y₃) ∘ ((f₁ <⊗> f₂) <⊗> f₃) ≡ (f₁ <⊗> (f₂ <⊗> f₃)) ∘ (α x₁ x₂ x₃))
    α-natural = NaturalTransformation.natural(NaturalIsomorphism.naturalTransformation([∃]-proof associator))

    υₗ-natural : ∀{x y}{f : x ⟶ y} → (υₗ(y) ∘ (id <⊗> f) ≡ f ∘ υₗ(x))
    υₗ-natural = NaturalTransformation.natural(NaturalIsomorphism.naturalTransformation([∃]-proof unitorₗ))

    υᵣ-natural : ∀{x y}{f : x ⟶ y} → (υᵣ(y) ∘ (f <⊗> id) ≡ f ∘ υᵣ(x))
    υᵣ-natural = NaturalTransformation.natural(NaturalIsomorphism.naturalTransformation([∃]-proof unitorᵣ))

    α⁻¹-natural : ∀{((x₁ , x₂) , x₃) ((y₁ , y₂) , y₃) : (Object ⨯ Object) ⨯ Object}
                   {(f₁ , f₂ , f₃) : ((x₁ ⟶ y₁) ⨯ ((x₂ ⟶ y₂) ⨯ (x₃ ⟶ y₃)))} →
                   ((α⁻¹ y₁ y₂ y₃) ∘ (f₁ <⊗> (f₂ <⊗> f₃)) ≡ ((f₁ <⊗> f₂) <⊗> f₃) ∘ (α⁻¹ x₁ x₂ x₃))
    α⁻¹-natural = NaturalTransformation.natural(NaturalIsomorphism.naturalTransformation([∃]-proof (invᴺᵀ associator)))

    υₗ⁻¹-natural : ∀{x y}{f : x ⟶ y} → (υₗ⁻¹(y) ∘ f ≡ (id <⊗> f) ∘ υₗ⁻¹(x))
    υₗ⁻¹-natural = NaturalTransformation.natural(NaturalIsomorphism.naturalTransformation([∃]-proof (invᴺᵀ unitorₗ)))

    υᵣ⁻¹-natural : ∀{x y}{f : x ⟶ y} → (υᵣ⁻¹(y) ∘ f ≡ (f <⊗> id) ∘ υᵣ⁻¹(x))
    υᵣ⁻¹-natural = NaturalTransformation.natural(NaturalIsomorphism.naturalTransformation([∃]-proof (invᴺᵀ unitorᵣ)))

    -- TODO: And the coherence conditions?

record Monoidalᶜᵃᵗ{ℓₒ}{ℓₘ}{ℓₑ} (C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}) : Type{Lvl.𝐒(ℓₒ Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    productFunctor : (C ⨯ᶜᵃᵗ C) →ᶠᵘⁿᶜᵗᵒʳ C
    unitObject : CategoryObject.Object(C)
    ⦃ monoidalCategory ⦄ : MonoidalCategory(productFunctor)(unitObject)

module _
  {C₁ : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} ⦃ (intro product₁ 𝟏₁) : Monoidalᶜᵃᵗ(C₁) ⦄
  {C₂ : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} ⦃ (intro product₂ 𝟏₂) : Monoidalᶜᵃᵗ(C₂) ⦄
  (functor@([∃]-intro F) : (C₁ →ᶠᵘⁿᶜᵗᵒʳ C₂))
  where

  instance _ = C₁
  instance _ = C₂

  open CategoryObject ⦃ … ⦄
  open Category ⦃ … ⦄
  open Category.ArrowNotation ⦃ … ⦄
  open Functor ⦃ … ⦄
  open MonoidalCategory ⦃ … ⦄

  -- Also called: Lax monoidal functor, applicative functor, idiom.
  record MonoidalFunctor : Type{Lvl.of(Type.of C₁)} where
    constructor intro
    field
      ε : 𝟏₂ ⟶ F(𝟏₁)
      Μ : (product₂ ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.map functor functor) →ᴺᵀ (functor ∘ᶠᵘⁿᶜᵗᵒʳ product₁)

    μ : ∀{x y} → ((F(x) ⊗ F(y)) ⟶ F(x ⊗ y))
    μ{x}{y} = [∃]-witness Μ (x , y)

    μ-natural : ∀{(x₁ , x₂) (y₁ , y₂) : Object ⦃ C₁ ⦄ ⨯ Object ⦃ C₁ ⦄}
                 {(f₁ , f₂) : ((x₁ ⟶ y₁) ⨯ (x₂ ⟶ y₂))} →
                 (μ ∘ (map(f₁) <⊗> map(f₂)) ≡ map(f₁ <⊗> f₂) ∘ μ)
    μ-natural = NaturalTransformation.natural([∃]-proof Μ)

    -- TODO: Coherence conditions

module _
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} ⦃ (intro product 𝟏) : Monoidalᶜᵃᵗ(C) ⦄
  (functor@([∃]-intro F) : (⟲ᶠᵘⁿᶜᵗᵒʳ C))
  where

  instance _ = C

  open CategoryObject ⦃ … ⦄
  open Category ⦃ … ⦄
  open Category.ArrowNotation ⦃ … ⦄
  open Functor ⦃ … ⦄
  open MonoidalCategory ⦃ … ⦄

  record TensorialStrength : Type{Lvl.of(Type.of C)} where
    constructor intro
    field
      Β : (product ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.mapRight functor) →ᴺᵀ (functor ∘ᶠᵘⁿᶜᵗᵒʳ product)

    β : ∀{x y} → ((x ⊗ F(y)) ⟶ F(x ⊗ y))
    β{x}{y} = [∃]-witness Β (x , y)

    β-natural : ∀{(x₁ , x₂) (y₁ , y₂) : Object ⦃ C ⦄ ⨯ Object ⦃ C ⦄}
                 {(f₁ , f₂) : ((x₁ ⟶ y₁) ⨯ (x₂ ⟶ y₂))} →
                 (β ∘ (f₁ <⊗> map(f₂)) ≡ map(f₁ <⊗> f₂) ∘ β)
    β-natural = NaturalTransformation.natural([∃]-proof Β)

  module TensorialStrengthenedMonoidalEndofunctor ⦃ monoidal : MonoidalFunctor(functor) ⦄ ⦃ strength : TensorialStrength ⦄ where
    open MonoidalFunctor(monoidal)
    open TensorialStrength(strength)

    Ι : idᶠᵘⁿᶜᵗᵒʳ →ᴺᵀ functor
    ∃.witness Ι x = {!!} ∘ μ{x}{𝟏} ∘ {!!}
    ∃.proof Ι = {!!}

    ι : ∀{x} → (x ⟶ F(x))
    ι{x} = [∃]-witness Ι x
