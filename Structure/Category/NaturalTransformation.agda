module Structure.Category.NaturalTransformation where

import      Functional as Fn
import      Lvl
open import Logic.Predicate
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Setoid
open import Type

open Category.ArrowNotation ⦃ … ⦄
open CategoryObject ⦃ … ⦄ hiding (identity)
open Functor ⦃ … ⦄

module _
  {ℓₗₒ ℓₗₘ ℓₗₑ ℓᵣₒ ℓᵣₘ ℓᵣₑ}
  {Cₗ : CategoryObject{ℓₗₒ}{ℓₗₘ}{ℓₗₑ}}
  {Cᵣ : CategoryObject{ℓᵣₒ}{ℓᵣₘ}{ℓᵣₑ}}
  where

  private instance _ = Cₗ
  private instance _ = Cᵣ

  module _ (([∃]-intro F₁ ⦃ functor₁ ⦄) ([∃]-intro F₂ ⦃ functor₂ ⦄) : Cₗ →ᶠᵘⁿᶜᵗᵒʳ Cᵣ) where
    -- A natural transformation is a family of morphisms on 
    record NaturalTransformation(η : ∀(x) → (F₁(x) ⟶ F₂(x))) : Type{Lvl.of(Type.of(Cₗ)) Lvl.⊔ Lvl.of(Type.of(Cᵣ))} where
      constructor intro
      field natural : ∀{x y}{f : x ⟶ y} → (η(y) ∘ map(f) ≡ map(f) ∘ η(x))

    _→ᴺᵀ_ = ∃(NaturalTransformation)
  _←ᴺᵀ_ = Fn.swap(_→ᴺᵀ_)
