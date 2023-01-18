module Structure.Category.NaturalIsomorphism.Functions where

open import Data.Tuple as Tuple using (_,_)
open import Functional.Instance using (infer)
open import DependentFunctional using () renaming (_∘_ to _∘ᶠⁿ_)
import      Lvl
open import Logic.Predicate
open import Logic.Propositional
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.NaturalIsomorphism
open import Structure.Category.NaturalTransformation
open import Structure.Category.Proofs
open import Structure.Categorical.Properties
open import Structure.Operator
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

  module _
    (F₁ᶠᵘⁿᶜᵗᵒʳ@([∃]-intro F₁ ⦃ functor₁ ⦄) F₂ᶠᵘⁿᶜᵗᵒʳ@([∃]-intro F₂ ⦃ functor₂ ⦄) : Cₗ →ᶠᵘⁿᶜᵗᵒʳ Cᵣ)
    (η : ∀(x) → (F₁(x) ⟷ F₂(x)))
    ⦃ naturalTransformation : NaturalTransformation(F₁ᶠᵘⁿᶜᵗᵒʳ)(F₂ᶠᵘⁿᶜᵗᵒʳ)(Tuple.right ∘ᶠⁿ η) ⦄
    ⦃ inverse : ∀{x} → Morphism.Inverse{Morphism = Morphism ⦃ Cᵣ ⦄}(_∘_)(id) (η(x)) ⦄
    where

    inverse-naturalTransformation : NaturalTransformation(F₂ᶠᵘⁿᶜᵗᵒʳ)(F₁ᶠᵘⁿᶜᵗᵒʳ)(Tuple.left ∘ᶠⁿ η)
    NaturalTransformation.natural inverse-naturalTransformation {x}{y}{f} =
      let
        η⁻¹ = Tuple.left ∘ᶠⁿ η
        η   = Tuple.right ∘ᶠⁿ η
      in
        η⁻¹(y) ∘ map(f)                     🝖[ _≡_ ]-[ Morphism.identityᵣ(_∘_)(id) ]-sym
        (η⁻¹(y) ∘ map(f)) ∘ id              🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(_) (Morphism.inverseᵣ(_∘_)(id) (η(x))(η⁻¹(x)) ⦃ [∧]-elimᵣ inverse ⦄) ]-sym
        (η⁻¹(y) ∘ map(f)) ∘ (η(x) ∘ η⁻¹(x)) 🝖[ _≡_ ]-[ associate4-231-121 (category ⦃ Cᵣ ⦄) ]-sym
        η⁻¹(y) ∘ ((map(f) ∘ η(x)) ∘ η⁻¹(x)) 🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(_) (congruence₂-₁(_∘_)(_) (NaturalTransformation.natural naturalTransformation)) ]-sym
        η⁻¹(y) ∘ ((η(y) ∘ map(f)) ∘ η⁻¹(x)) 🝖[ _≡_ ]-[ associate4-231-121 (category ⦃ Cᵣ ⦄) ]
        (η⁻¹(y) ∘ η(y)) ∘ (map(f) ∘ η⁻¹(x)) 🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(_) (Morphism.inverseₗ(_∘_)(id) (η(y))(η⁻¹(y)) ⦃ [∧]-elimₗ inverse ⦄) ]
        id ∘ (map(f) ∘ η⁻¹(x))              🝖[ _≡_ ]-[ Morphism.identityₗ(_∘_)(id) ]
        map(f) ∘ η⁻¹(x)                     🝖-end

    NaturalIsomorphism-introᵣ : NaturalIsomorphism(F₁ᶠᵘⁿᶜᵗᵒʳ)(F₂ᶠᵘⁿᶜᵗᵒʳ) η
    NaturalIsomorphism.naturalTransformationₗ NaturalIsomorphism-introᵣ = inverse-naturalTransformation
    NaturalIsomorphism.naturalTransformationᵣ NaturalIsomorphism-introᵣ = naturalTransformation
    NaturalIsomorphism.inverse                NaturalIsomorphism-introᵣ = inverse

  module _
    (F₁ᶠᵘⁿᶜᵗᵒʳ@([∃]-intro F₁ ⦃ functor₁ ⦄) F₂ᶠᵘⁿᶜᵗᵒʳ@([∃]-intro F₂ ⦃ functor₂ ⦄) : Cₗ →ᶠᵘⁿᶜᵗᵒʳ Cᵣ)
    (η : ∀(x) → (F₁(x) ⟷ F₂(x)))
    ⦃ naturalTransformation : NaturalTransformation(F₂ᶠᵘⁿᶜᵗᵒʳ)(F₁ᶠᵘⁿᶜᵗᵒʳ)(Tuple.left ∘ᶠⁿ η) ⦄
    ⦃ inverse : ∀{x} → Morphism.Inverse{Morphism = Morphism ⦃ Cᵣ ⦄}(_∘_)(id) (η(x)) ⦄
    where

    NaturalIsomorphism-introₗ : NaturalIsomorphism(F₁ᶠᵘⁿᶜᵗᵒʳ)(F₂ᶠᵘⁿᶜᵗᵒʳ) η
    NaturalIsomorphism.naturalTransformationₗ NaturalIsomorphism-introₗ = naturalTransformation
    NaturalIsomorphism.naturalTransformationᵣ NaturalIsomorphism-introₗ = inverse-naturalTransformation(F₂ᶠᵘⁿᶜᵗᵒʳ)(F₁ᶠᵘⁿᶜᵗᵒʳ) (Tuple.swap ∘ᶠⁿ η) ⦃ naturalTransformation ⦄ ⦃ Tuple.swap inverse ⦄
    NaturalIsomorphism.inverse                NaturalIsomorphism-introₗ = inverse

    NaturalIsomorphism-inverse : ∀{η} → ⦃ ni : NaturalIsomorphism(F₁ᶠᵘⁿᶜᵗᵒʳ)(F₂ᶠᵘⁿᶜᵗᵒʳ)(η) ⦄ → NaturalIsomorphism(F₂ᶠᵘⁿᶜᵗᵒʳ)(F₁ᶠᵘⁿᶜᵗᵒʳ)(Tuple.swap ∘ᶠⁿ η) -- TODO: Should not be an instance parameter (20220415: Why not?)
    NaturalIsomorphism-inverse = intro ⦃ inverse = Tuple.swap infer ⦄

  private variable F₁ F₂ : Cₗ →ᶠᵘⁿᶜᵗᵒʳ Cᵣ

  invᴺᵀ : (F₁ ↔ᴺᵀ F₂) → (F₂ ↔ᴺᵀ F₁)
  invᴺᵀ {F₁ = F₁}{F₂ = F₂} ([∃]-intro _) = [∃]-intro _ ⦃ NaturalIsomorphism-inverse F₁ F₂ _ ⦄
