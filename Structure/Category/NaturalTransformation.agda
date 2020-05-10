module Structure.Category.NaturalTransformation where

open import Functional           using () renaming (id to idᶠⁿ)
open import Functional.Dependent using () renaming (_∘_ to _∘ᶠⁿ_)
import      Lvl
open import Logic
open import Logic.Predicate
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Setoid.WithLvl
open import Type

module _
  {ℓₗₒ ℓₗₘ ℓₗₑ ℓᵣₒ ℓᵣₘ ℓᵣₑ}
  {catₗ : CategoryObject{ℓₗₒ}{ℓₗₘ}{ℓₗₑ}}
  {catᵣ : CategoryObject{ℓᵣₒ}{ℓᵣₘ}{ℓᵣₑ}}
  (([∃]-intro F₁ ⦃ functor₁ ⦄) : catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ)
  (([∃]-intro F₂ ⦃ functor₂ ⦄) : catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ)
  where

  open Category.ArrowNotation ⦃ … ⦄
  open Category ⦃ … ⦄ hiding (identity)
  open CategoryObject ⦃ … ⦄
  open Functor ⦃ … ⦄

  private instance _ = catₗ
  private instance _ = catᵣ

  -- A natural transformation is a family of morphisms on 
  record NaturalTransformation (η : ∀(x) → (F₁(x) ⟶ F₂(x))) : Type{Lvl.of(type-of(catₗ)) Lvl.⊔ Lvl.of(type-of(catᵣ))} where
    constructor intro
    field natural : ∀{x y}{f : x ⟶ y} → (η(y) ∘ map(f) ≡ map(f) ∘ η(x))

  _→ᴺᵀ_ = ∃(NaturalTransformation)
