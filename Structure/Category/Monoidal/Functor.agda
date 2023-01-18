module Structure.Category.Monoidal.Functor where

import      Lvl
open import Data.Tuple as Tuple using (_,_ ; _⨯_)
open import Data.Tuple.Category
open import Data.Tuple.Equivalence
open import DependentFunctional using () renaming (_∘_ to _∘ᶠⁿ_)
import      Function.Equals
open        Function.Equals.Dependent
import      Functional as Fn
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Category
open import Structure.Category.Functor
import      Structure.Category.Functor.Functors as Functors
open import Structure.Category.Monoidal
open import Structure.Category.NaturalTransformation
open import Structure.Category.NaturalTransformation.NaturalTransformations as NaturalTransformations
open import Syntax.Function
open import Type

private variable ℓ ℓₒ ℓₘ ℓₑ ℓₒ₁ ℓₘ₁ ℓₑ₁ ℓₒ₂ ℓₘ₂ ℓₑ₂ : Lvl.Level
private variable Obj : Type{ℓ}
private variable Morphism : Obj → Obj → Type{ℓ}

open Functors.Wrapped

module _
  {C₁ : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} ⦃ M₁@(intro ⊗ᶠᵘⁿᶜᵗᵒʳ₁ 𝟏₁) : Monoidalᶜᵃᵗ(C₁) ⦄
  {C₂ : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} ⦃ M₂@(intro ⊗ᶠᵘⁿᶜᵗᵒʳ₂ 𝟏₂) : Monoidalᶜᵃᵗ(C₂) ⦄
  (Fᶠᵘⁿᶜᵗᵒʳ@([∃]-intro F) : (C₁ →ᶠᵘⁿᶜᵗᵒʳ C₂))
  where

  instance _ = C₁
  instance _ = C₂

  open CategoryObject ⦃ … ⦄
  open Category.ArrowNotation ⦃ … ⦄
  open Functor ⦃ … ⦄
  open MonoidalCategory ⦃ … ⦄
  open NaturalTransformations.Raw(C₁)(C₂)

  -- Also called: Lax monoidal functor
  record MonoidalFunctor : Type{Lvl.of(Type.of C₁)} where
    constructor intro
    field
      ε : 𝟏₂ ⟶ F(𝟏₁)
      Μ : (⊗ᶠᵘⁿᶜᵗᵒʳ₂ Tupleᶜᵃᵗ.on₂ Fᶠᵘⁿᶜᵗᵒʳ) →ᴺᵀ (Fᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ ⊗ᶠᵘⁿᶜᵗᵒʳ₁)

    μ : ∀(x)(y) → ((F(x) ⊗ F(y)) ⟶ F(x ⊗ y))
    μ x y = [∃]-witness Μ (x , y)

    μ-natural : ∀{(x₁ , x₂) (y₁ , y₂) : Object ⦃ C₁ ⦄ ⨯ Object ⦃ C₁ ⦄}
                 {(f₁ , f₂) : ((x₁ ⟶ y₁) ⨯ (x₂ ⟶ y₂))} →
                 (μ(y₁)(y₂) ∘ (map(f₁) <⊗> map(f₂)) ≡ map(f₁ <⊗> f₂) ∘ μ(x₁)(x₂))
    μ-natural = NaturalTransformation.natural([∃]-proof Μ)

    -- Coherence conditions.
    field
      associativity-condition : ∀{x y z} → (map(α(x)(y)(z)) ∘ μ(x ⊗ y)(z) ∘ (μ(x)(y) <⊗> id) ≡ μ(x)(y ⊗ z) ∘ (id <⊗> μ(y)(z)) ∘ α(F(x))(F(y))(F(z)))
      unitalityₗ-condition    : ∀{x} → (map(υₗ(x)) ∘ μ(𝟏₁)(x) ∘ (ε <⊗> id) ≡ υₗ(F(x))) -- ((map ∘ᶠⁿ υₗ) ∘ᴺᵀ μ(𝟏₁) ∘ᴺᵀ (x ↦ ε <⊗> id{x = F(x)})) ⊜ (υₗ ∘ᶠⁿ F)
      unitalityᵣ-condition    : ∀{x} → (map(υᵣ(x)) ∘ μ(x)(𝟏₁) ∘ (id <⊗> ε) ≡ υᵣ(F(x)))

module _
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} ⦃ M@(intro ⊗ᶠᵘⁿᶜᵗᵒʳ 𝟏) : Monoidalᶜᵃᵗ(C) ⦄
  (Fᶠᵘⁿᶜᵗᵒʳ@([∃]-intro F) : (⟲ᶠᵘⁿᶜᵗᵒʳ C))
  where

  instance _ = C

  open CategoryObject ⦃ … ⦄
  open Category.ArrowNotation ⦃ … ⦄
  open Functor ⦃ … ⦄
  open MonoidalCategory ⦃ … ⦄

  record TensorialStrength : Type{Lvl.of(Type.of C)} where
    constructor intro
    field
      Β : (⊗ᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.mapRight Fᶠᵘⁿᶜᵗᵒʳ) →ᴺᵀ (Fᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ ⊗ᶠᵘⁿᶜᵗᵒʳ)

    β : ∀(x)(y) → ((x ⊗ F(y)) ⟶ F(x ⊗ y))
    β x y = [∃]-witness Β (x , y)

    β-natural : ∀{(x₁ , x₂) (y₁ , y₂) : Object ⦃ C ⦄ ⨯ Object ⦃ C ⦄}
                 {(f₁ , f₂) : ((x₁ ⟶ y₁) ⨯ (x₂ ⟶ y₂))} →
                 (β y₁ y₂ ∘ (f₁ <⊗> map(f₂)) ≡ map(f₁ <⊗> f₂) ∘ β x₁ x₂)
    β-natural = NaturalTransformation.natural([∃]-proof Β)

    -- Coherence conditions.
    field
      associativity-condition : ∀{x y z} → (map(α(x)(y)(z)) ∘ β(x ⊗ y)(z) ≡ β(x)(y ⊗ z) ∘ (id <⊗> β(y)(z)) ∘ α(x)(y)(F(z)))
      unitalityₗ-condition    : ∀{x} → (map(υₗ(x)) ∘ β(𝟏)(x) ≡ υₗ(F(x)))

  {-
  -- Also called: Applicative functor, idiom.
  module TensorialStrengthenedMonoidalEndofunctor ⦃ monoidal : MonoidalFunctor(Fᶠᵘⁿᶜᵗᵒʳ) ⦄ ⦃ strength : TensorialStrength ⦄ where
    open MonoidalFunctor(monoidal)
    open TensorialStrength(strength)
    open NaturalTransformations.Wrapped

    Ι : idᶠᵘⁿᶜᵗᵒʳ →ᴺᵀ Fᶠᵘⁿᶜᵗᵒʳ
    -- Ι = _∘ᴺᵀ_ {F₁ = idᶠᵘⁿᶜᵗᵒʳ}{F₂ = {!!}}{F₃ = Fᶠᵘⁿᶜᵗᵒʳ} {!!} ({!Β!} ∘ᴺᵀ {!!} ∘ᴺᵀ ($ₗᴺᵀ unitorᵣ)) -- TODO: Maybe need the other kinds of nt-composition to express this?
    ∃.witness Ι x = map(υᵣ(x)) ∘ β(x)(𝟏) ∘ (id <⊗> ε) ∘ υᵣ⁻¹(x) -- TODO: Not a good way of doing it. Then one has to prove that this is a natural transformation manually.
    ∃.proof Ι = {!!}

    ι : ∀{x} → (x ⟶ F(x))
    ι{x} = [∃]-witness Ι x

    {-
    x
    x ⊗ 𝟏
    x ⊗ F(𝟏)
    F(x ⊗ 𝟏)
    F(x)
    -}
  -}
