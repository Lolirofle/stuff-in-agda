module Structure.Category.NaturalIsomorphism where

open import Functional          as Fn using () renaming (id to idᶠⁿ)
open import DependentFunctional using () renaming (_∘_ to _∘ᶠⁿ_)
import      Lvl
open import Logic
open import Logic.Predicate
open import Logic.Propositional
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.NaturalTransformation
open import Structure.Category.Proofs
open import Structure.Categorical.Properties
open import Structure.Operator
open import Structure.Setoid
open import Syntax.Function
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
    record NaturalIsomorphism(η : ∀(x) → (F₁(x) ⟶ F₂(x))) : Type{Lvl.of(Type.of(Cₗ)) Lvl.⊔ Lvl.of(Type.of(Cᵣ))} where -- TODO: Consider defining this by two natural tranformations instead
      constructor intro
      field
        ⦃ naturalTransformation ⦄ : NaturalTransformation(F₁ᶠᵘⁿᶜᵗᵒʳ)(F₂ᶠᵘⁿᶜᵗᵒʳ)(η)
        ⦃ components-isomorphism ⦄ : ∀{x} → Morphism.Isomorphism{Morphism = Morphism ⦃ Cᵣ ⦄}(_∘_)(id) (η(x))

      inv : ∀(x) → (F₁(x) ⟵ F₂(x))
      inv(x) = [∃]-witness (components-isomorphism {x})

      instance
        inverseₗ : ∀{x} → Morphism.Inverseₗ(_∘_)(id) (η(x))(inv(x))
        inverseₗ{x} = [∧]-elimₗ([∃]-proof (components-isomorphism{x}))

      instance
        inverseᵣ : ∀{x} → Morphism.Inverseᵣ(_∘_)(id) (η(x))(inv(x))
        inverseᵣ{x} = [∧]-elimᵣ([∃]-proof (components-isomorphism{x}))

    _↔ᴺᵀ_ = ∃(NaturalIsomorphism)

  module _ (F₁@([∃]-intro f₁) F₂@([∃]-intro f₂) : Cₗ →ᶠᵘⁿᶜᵗᵒʳ Cᵣ) where
    -- open NaturalIsomorphism ⦃ … ⦄

    NaturalIsomorphism-inverse : ∀{η} → ⦃ ni : NaturalIsomorphism(F₁)(F₂)(η) ⦄ → NaturalIsomorphism(F₂)(F₁)(x ↦ Morphism.inv(_∘_)(id) (η(x))) -- TODO: Should not be an instance parameter
    NaturalTransformation.natural (NaturalIsomorphism.naturalTransformation (NaturalIsomorphism-inverse {η} ⦃ ni ⦄)) {x} {y} {f} =
      let open NaturalIsomorphism(ni) renaming (inv to η⁻¹)
      in
        η⁻¹(y) ∘ map(f)                     🝖[ _≡_ ]-[ Morphism.identityᵣ(_∘_)(id) ]-sym
        (η⁻¹(y) ∘ map(f)) ∘ id              🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(_) (Morphism.inverseᵣ(_∘_)(id) (η(x))(η⁻¹(x)) ⦃ inverseᵣ ⦄) ]-sym
        (η⁻¹(y) ∘ map(f)) ∘ (η(x) ∘ η⁻¹(x)) 🝖[ _≡_ ]-[ associate4-231-121 (category ⦃ Cᵣ ⦄) ]-sym
        η⁻¹(y) ∘ ((map(f) ∘ η(x)) ∘ η⁻¹(x)) 🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(_) (congruence₂-₁(_∘_)(_) (NaturalTransformation.natural(NaturalIsomorphism.naturalTransformation ni))) ]-sym
        η⁻¹(y) ∘ ((η(y) ∘ map(f)) ∘ η⁻¹(x)) 🝖[ _≡_ ]-[ associate4-231-121 (category ⦃ Cᵣ ⦄) ]
        (η⁻¹(y) ∘ η(y)) ∘ (map(f) ∘ η⁻¹(x)) 🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(_) (Morphism.inverseₗ(_∘_)(id) (η(y))(η⁻¹(y)) ⦃ inverseₗ ⦄) ]
        id ∘ (map(f) ∘ η⁻¹(x))              🝖[ _≡_ ]-[ Morphism.identityₗ(_∘_)(id) ]
        map(f) ∘ η⁻¹(x)                     🝖-end
    NaturalIsomorphism.components-isomorphism (NaturalIsomorphism-inverse {η}) {x} = inverse-isomorphism category (η(x))

  private variable F₁ F₂ : Cₗ →ᶠᵘⁿᶜᵗᵒʳ Cᵣ

  invᴺᵀ : (F₁ ↔ᴺᵀ F₂) → (F₂ ↔ᴺᵀ F₁)
  invᴺᵀ {F₁ = F₁}{F₂ = F₂} ([∃]-intro _) = [∃]-intro _ ⦃ NaturalIsomorphism-inverse F₁ F₂ ⦄

  $ᵣᴺᵀ : (F₁ ↔ᴺᵀ F₂) → (F₁ →ᴺᵀ F₂)
  $ᵣᴺᵀ ([∃]-intro η) = [∃]-intro η

  $ₗᴺᵀ : (F₁ ↔ᴺᵀ F₂) → (F₁ ←ᴺᵀ F₂)
  $ₗᴺᵀ = $ᵣᴺᵀ Fn.∘ invᴺᵀ
