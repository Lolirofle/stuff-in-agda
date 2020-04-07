module Structure.Category.Monoidal where

import      Lvl
open import Data.Tuple as Tuple
open import Data.Tuple.Category
open import Data.Tuple.Equiv
import      Functional as Fn
open import Logic.Predicate
open import Sets.Setoid
open import Structure.Category
open import Structure.Category.Functor
import      Structure.Category.Functor.Functors as Functors
open import Structure.Category.NaturalTransformation
open import Syntax.Function
open import Type

private variable ℓ : Lvl.Level
private variable Obj : Type{ℓ}
private variable Morphism : Obj → Obj → Type{ℓ}

open Functors.Raw

module _
  ⦃ morphism-equiv : ∀{x y : Obj} → Equiv(Morphism x y) ⦄
  {C : Category(Morphism)}
  (([∃]-intro F ⦃ funct ⦄) : ((C ⨯ᶜᵃᵗ C) →ᶠᵘⁿᶜᵗᵒʳ C))
  (𝟏 : Obj)
  where

  open Category.ArrowNotation(C)

  -- TODO: Implement and generalize so that C₁ C₂ C₃
  postulate associateLeftFunctor : Functor(C ⨯ᶜᵃᵗ (C ⨯ᶜᵃᵗ C))((C ⨯ᶜᵃᵗ C) ⨯ᶜᵃᵗ C) (associateLeft)
  postulate tupleFunctor : ∀{F}{G} → Functor(C)(C) (F) → Functor(C)(C) (G) → Functor(C)(C ⨯ᶜᵃᵗ C) (x ↦ (F(x)) , G(x))

  record MonoidalCategory : Type{Lvl.of(type-of C)} where
    constructor intro

    _⊗_ = curry F

    field
      -- associator : ((\{(x , y , z) → F(F(x , y) , z)}) →ᴺᵀ (\{(x , y , z) → F(x , F(y , z))}))
      -- associator : ((F ∘ᶠᵘⁿᶜᵗᵒʳ (Tuple.map F idᶠᵘⁿᶜᵗᵒʳ) ∘ᶠᵘⁿᶜᵗᵒʳ associateLeft) →ᴺᵀ (F ∘ᶠᵘⁿᶜᵗᵒʳ (Tuple.map idᶠᵘⁿᶜᵗᵒʳ F)))
      associator : ((\{(x , y , z) → ((x ⊗ y) ⊗ z)}) →ᴺᵀ (\{(x , y , z) → (x ⊗ (y ⊗ z))}))
        ⦃ Functors.composition funct (Functors.composition (productFunctor funct Functors.identity) associateLeftFunctor) ⦄
        ⦃ Functors.composition funct (productFunctor Functors.identity funct) ⦄

      unitorₗ : ((𝟏 ⊗_) →ᴺᵀ idᶠᵘⁿᶜᵗᵒʳ)
        ⦃ Functors.composition funct (tupleFunctor (Functors.constant 𝟏) Functors.identity) ⦄
        ⦃ Functors.identity ⦄

      unitorᵣ : ((_⊗ 𝟏) →ᴺᵀ idᶠᵘⁿᶜᵗᵒʳ)
        ⦃ Functors.composition funct (tupleFunctor Functors.identity (Functors.constant 𝟏)) ⦄
        ⦃ Functors.identity ⦄

      -- TODO: Triangle identity, pentagon identity?

  -- TODO: Generalize for different categories
  {-record LaxMonoidalFunctor (A B : MonoidalCategory) (F : Obj → Obj) : Type{Lvl.of(type-of C)} where
    constructor intro
    field
      ⦃ functor ⦄ : Functor(C)(C) (F)

    private instance _ = A
    private instance _ = B
    open MonoidalCategory ⦃ … ⦄

    field
      ε : 𝟏 ⟶ F(𝟏)
      μ : ∀{x y : Obj} → ((F(x) ⊗ F(y)) ⟶ F(x ⊗ y))

    field
      μ-naturalTransformation : NaturalTransformation ? ? (μ)
  -}
