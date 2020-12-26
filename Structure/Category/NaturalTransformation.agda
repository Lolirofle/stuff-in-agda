module Structure.Category.NaturalTransformation where

open import Functional           using () renaming (id to idᶠⁿ)
open import Functional.Dependent using () renaming (_∘_ to _∘ᶠⁿ_)
import      Lvl
open import Logic
open import Logic.Predicate
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.Proofs
open import Structure.Categorical.Properties
open import Structure.Setoid
open import Syntax.Function
open import Type

open Category.ArrowNotation ⦃ … ⦄
open Category ⦃ … ⦄ hiding (identity)
open CategoryObject ⦃ … ⦄
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

    record NaturalIsomorphism(η : ∀(x) → (F₁(x) ⟶ F₂(x))) : Type{Lvl.of(Type.of(Cₗ)) Lvl.⊔ Lvl.of(Type.of(Cᵣ))} where -- TODO: Consider defining this by two natural tranformations instead
      constructor intro
      field
        ⦃ naturalTransformation ⦄ : NaturalTransformation(η)
        ⦃ components-isomorphism ⦄ : ∀{x} → Morphism.Isomorphism{Morphism = Morphism ⦃ Cᵣ ⦄}(_∘_)(id) (η(x))

    _→ᴺᵀ_ = ∃(NaturalTransformation)
    _↔ᴺᵀ_ = ∃(NaturalIsomorphism)

  module _ (F₁ F₂ : Cₗ →ᶠᵘⁿᶜᵗᵒʳ Cᵣ) where
    open NaturalIsomorphism ⦃ … ⦄

    NaturalIsomorphism-inverse : ∀{η} → ⦃ ni : NaturalIsomorphism(F₁)(F₂)(η) ⦄ → NaturalIsomorphism(F₂)(F₁)(x ↦ Morphism.inv(_∘_)(id) (η(x))) -- TODO: Should not be an instance parameter
    NaturalTransformation.natural (NaturalIsomorphism.naturalTransformation NaturalIsomorphism-inverse) {x} {y} {f} = a where
      postulate a : ∀{a} → a -- TODO: Prove, and also move natural isomorphisms to a new file
    NaturalIsomorphism.components-isomorphism (NaturalIsomorphism-inverse {η}) {x} = inverse-isomorphism category (η(x))

  module _ {F₁ F₂ : Cₗ →ᶠᵘⁿᶜᵗᵒʳ Cᵣ} where
    open NaturalIsomorphism ⦃ … ⦄

    invᴺᵀ : (F₁ ↔ᴺᵀ F₂) → (F₂ ↔ᴺᵀ F₁)
    invᴺᵀ ([∃]-intro _) = [∃]-intro _ ⦃ NaturalIsomorphism-inverse F₁ F₂ ⦄
