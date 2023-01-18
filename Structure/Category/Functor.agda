module Structure.Category.Functor where

open import Functional using (_on₂_)
import      Lvl
open import Logic.Predicate
open import Structure.Categorical.Functor.Properties
open import Structure.Category
open import Structure.Function
import      Structure.Relator.Names as Names
open import Structure.Setoid
open import Type

private variable ℓ ℓₒ ℓₘ ℓₗₒ ℓₗₘ ℓᵣₒ ℓᵣₘ ℓₑ ℓₗₑ ℓᵣₑ : Lvl.Level
private variable Obj Objₗ Objᵣ : Type{ℓ}
private variable _⟶_ _⟶ₗ_ _⟶ᵣ_ : Objₗ → Objᵣ → Type{ℓ}

module _
  ⦃ morphism-equivₗ : ∀{x y : Objₗ} → Equiv{ℓₗₑ}(_⟶ₗ_ x y) ⦄
  ⦃ morphism-equivᵣ : ∀{x y : Objᵣ} → Equiv{ℓᵣₑ}(_⟶ᵣ_ x y) ⦄
  (Categoryₗ : Category(_⟶ₗ_))
  (Categoryᵣ : Category(_⟶ᵣ_))
  where

  -- A covariant functor.
  -- A mapping which transforms objects and morphisms from one category to another while "preserving" the categorical structure.
  -- A homomorphism between categories.
  -- In the context of equivalence relations instead of categories, this is the "function"/"congruence" property of the function `F`.
  record Functor (F : Objₗ → Objᵣ) : Type{Lvl.of(Type.of(Categoryₗ)) Lvl.⊔ Lvl.of(Type.of(Categoryᵣ))} where
    constructor intro
    open Category ⦃ … ⦄
    private instance _ = Categoryₗ
    private instance _ = Categoryᵣ

    field
      -- Morphs/Transforms morphisms from the left category to the right category.
      -- ∀{x y : Objₗ} → (x ⟶ y) → (F(x) ⟶ F(y))
      map : Names.Sub₂(_⟶ₗ_) ((_⟶ᵣ_) on₂ F)

    field
      ⦃ map-function ⦄     : ∀{x y} → Function(map{x}{y})
      ⦃ op-preserving ⦄    : ∀{x y z : Objₗ} → Preserving₂(_⟶ₗ_)(_⟶ᵣ_) map (_∘_ {x = x}{y = y}{z = z}) (_∘_)
      ⦃ id-preserving ⦄    : ∀{x : Objₗ} → Preserving₀(_⟶ₗ_)(_⟶ᵣ_) map (id{x = x}) id

    open import Structure.Categorical.Properties
    open import Structure.Function.Domain

    Faithful      = ∀{x y} → Injective (map{x}{y}) -- TODO: F also? Not sure
    Full          = ∀{x y} → Surjective(map{x}{y})
    FullyFaithful = ∀{x y} → Bijective (map{x}{y})
    -- TODO: Conservative  = ∀{x y : Objₗ}{f : x ⟶ y} → Morphism.Isomorphism(\{x} → _∘_ {x = x})(\{x} → id{x = x})(map f) → Morphism.Isomorphism(\{x} → _∘_ {x = x})(id)(f)

module _
  ⦃ morphism-equiv : ∀{x y : Obj} → Equiv{ℓₑ}(_⟶_ x y) ⦄
  (Category : Category(_⟶_))
  where

  Endofunctor = Functor(Category)(Category)
  module Endofunctor = Functor{Categoryₗ = Category}{Categoryᵣ = Category}

_→ᶠᵘⁿᶜᵗᵒʳ_ : CategoryObject{ℓₗₒ}{ℓₗₘ}{ℓₗₑ} → CategoryObject{ℓᵣₒ}{ℓᵣₘ}{ℓᵣₑ} → Type
catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ = ∃(Functor (CategoryObject.category(catₗ)) ((CategoryObject.category(catᵣ))))

⟲ᶠᵘⁿᶜᵗᵒʳ_ : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ} → Type
⟲ᶠᵘⁿᶜᵗᵒʳ cat = cat →ᶠᵘⁿᶜᵗᵒʳ cat
