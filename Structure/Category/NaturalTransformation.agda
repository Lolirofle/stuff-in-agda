module Structure.Category.NaturalTransformation where

open import Functional           using () renaming (id to idᶠⁿ)
open import Functional.Dependent using () renaming (_∘_ to _∘ᶠⁿ_)
import      Lvl
open import Logic
open import Logic.Predicate
open import Sets.Setoid
open import Structure.Category
open import Structure.Category.Functor
open import Type

private variable ℓₒ ℓₘ ℓₘₗ ℓₘᵣ : Lvl.Level
private variable Obj Objₗ Objᵣ : Type{ℓₒ}
private variable Morphism Morphismₗ Morphismᵣ : Obj → Obj → Type{ℓₘ}

module _
  ⦃ obj-equivₗ : Equiv(Objₗ) ⦄
  ⦃ obj-equivᵣ : Equiv(Objᵣ) ⦄
  ⦃ morphism-equivₗ : ∀{x y : Objₗ} → Equiv(Morphismₗ x y) ⦄
  ⦃ morphism-equivᵣ : ∀{x y : Objᵣ} → Equiv(Morphismᵣ x y) ⦄
  {catₗ : Category(Morphismₗ)}
  {catᵣ : Category(Morphismᵣ)}
  where

  open Category.ArrowNotation ⦃ … ⦄
  open Category ⦃ … ⦄ hiding (identity)
  open Functor ⦃ … ⦄

  private instance _ = catₗ
  private instance _ = catᵣ

  module _
    (([∃]-intro F₁ ⦃ functor₁ ⦄) : catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ)
    (([∃]-intro F₂ ⦃ functor₂ ⦄) : catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ)
    where

    record NaturalTransformation (η : (x : Objₗ) → (F₁(x) ⟶ F₂(x))) : Type{Lvl.of(type-of(catₗ)) Lvl.⊔ Lvl.of(type-of(catᵣ))} where
      field
        natural : ∀{x y : Objₗ}{f : x ⟶ y} → (η(y) ∘ map(f) ≡ map(f) ∘ η(x))

  module _
    (F₁ : Objₗ → Objᵣ)
    (F₂ : Objₗ → Objᵣ)
    ⦃ functor₁ : Functor catₗ catᵣ F₁ ⦄
    ⦃ functor₂ : Functor catₗ catᵣ F₂ ⦄
    where

    _→ᴺᵀ_ = ∃(NaturalTransformation([∃]-intro F₁)([∃]-intro F₂))
