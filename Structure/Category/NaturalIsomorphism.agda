module Structure.Category.NaturalIsomorphism where

open import Data.Tuple as Tuple using (_,_)
open import DependentFunctional using () renaming (_∘_ to _∘ᶠⁿ_)
import      Lvl
open import Logic.Predicate
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.NaturalTransformation
open import Structure.Categorical.Properties
open import Structure.Setoid
open import Syntax.Transitivity
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
  private open module Equivₗ{x}{y} = Equiv(CategoryObject.morphism-equiv(Cₗ){x}{y}) using ()
  private open module Equivᵣ{x}{y} = Equiv(CategoryObject.morphism-equiv(Cᵣ){x}{y}) using ()

  module _ (F₁ᶠᵘⁿᶜᵗᵒʳ@([∃]-intro F₁ ⦃ functor₁ ⦄) F₂ᶠᵘⁿᶜᵗᵒʳ@([∃]-intro F₂ ⦃ functor₂ ⦄) : Cₗ →ᶠᵘⁿᶜᵗᵒʳ Cᵣ) where
    record NaturalIsomorphism(η : ∀(x) → (F₁(x) ⟷ F₂(x))) : Type{Lvl.of(Type.of(Cₗ)) Lvl.⊔ Lvl.of(Type.of(Cᵣ))} where
      constructor intro

      left : ∀(x) → (F₁(x) ⟵ F₂(x))
      left = Tuple.left ∘ᶠⁿ η

      right : ∀(x) → (F₁(x) ⟶ F₂(x))
      right = Tuple.right ∘ᶠⁿ η

      swapped : ∀(x) → (F₂(x) ⟷ F₁(x))
      swapped = Tuple.swap ∘ᶠⁿ η

      field
        ⦃ naturalTransformationₗ ⦄ : NaturalTransformation(F₂ᶠᵘⁿᶜᵗᵒʳ)(F₁ᶠᵘⁿᶜᵗᵒʳ)(left)
        ⦃ naturalTransformationᵣ ⦄ : NaturalTransformation(F₁ᶠᵘⁿᶜᵗᵒʳ)(F₂ᶠᵘⁿᶜᵗᵒʳ)(right)
        ⦃ inverse ⦄                : ∀{x} → Morphism.Inverse{Morphism = Morphism ⦃ Cᵣ ⦄}(_∘_)(id) (η(x))

    _↔ᴺᵀ_ = ∃(NaturalIsomorphism)

  private variable F₁ F₂ : Cₗ →ᶠᵘⁿᶜᵗᵒʳ Cᵣ

  $ₗᴺᵀ : (F₁ ↔ᴺᵀ F₂) → (F₁ ←ᴺᵀ F₂)
  $ₗᴺᵀ ([∃]-intro η) = [∃]-intro (Tuple.left ∘ᶠⁿ η)

  $ᵣᴺᵀ : (F₁ ↔ᴺᵀ F₂) → (F₁ →ᴺᵀ F₂)
  $ᵣᴺᵀ ([∃]-intro η) = [∃]-intro (Tuple.right ∘ᶠⁿ η)
