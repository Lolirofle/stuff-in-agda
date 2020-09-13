module Structure.Category.Functor where

open import Functional using (_on₂_)
open import Lang.Instance
import      Lvl
open import Logic.Predicate
open import Structure.Category
open import Structure.Function
open import Structure.Function.Multi
import      Structure.Relator.Names as Names
open import Structure.Setoid.WithLvl
open import Syntax.Function
open import Type

private variable ℓ ℓₒ ℓₘ ℓₗₒ ℓₗₘ ℓᵣₒ ℓᵣₘ ℓₑ ℓₗₑ ℓᵣₑ : Lvl.Level
private variable Obj Objₗ Objᵣ : Type{ℓ}
private variable Morphism Morphismₗ Morphismᵣ : Objₗ → Objᵣ → Type{ℓ}

module _
  ⦃ morphism-equivₗ : ∀{x y : Objₗ} → Equiv{ℓₗₑ}(Morphismₗ x y) ⦄
  ⦃ morphism-equivᵣ : ∀{x y : Objᵣ} → Equiv{ℓᵣₑ}(Morphismᵣ x y) ⦄
  (Categoryₗ : Category(Morphismₗ))
  (Categoryᵣ : Category(Morphismᵣ))
  where

  -- A covariant functor.
  -- A mapping which transforms objects and morphisms from one category to another while "preserving" the categorical structure.
  -- A homomorphism between categories.
  -- In the context of equivalence relations instead of categories, this is the "function"/"congruence" property of the function `F`.
  record Functor (F : Objₗ → Objᵣ) : Type{Lvl.of(Type.of(Categoryₗ)) Lvl.⊔ Lvl.of(Type.of(Categoryᵣ))} where
    constructor intro
    open Category ⦃ … ⦄
    open Category.ArrowNotation ⦃ … ⦄
    private instance _ = Categoryₗ
    private instance _ = Categoryᵣ

    field
      -- Morphs/Transforms morphisms from the left category to the right category.
      -- ∀{x y : Objₗ} → (x ⟶ y) → (F(x) ⟶ F(y))
      map : Names.Subrelation(_⟶_) ((_⟶_) on₂ F)

    field
      ⦃ map-function ⦄     : ∀{x y} → Function(map{x}{y})
      ⦃ op-preserving ⦄    : ∀{x y z : Objₗ}{f : y ⟶ z}{g : x ⟶ y} → (map(f ∘ g) ≡ map(f) ∘ map(g))
      ⦃ id-preserving ⦄    : ∀{x : Objₗ} → Names.Preserving₀(map{x})(id)(id) --(map(id {x = x}) ≡ id)

    open import Structure.Categorical.Properties
    open import Structure.Function.Domain

    Faithful      = ∀{x y} → Injective (map{x}{y}) -- TODO: F also? Not sure
    Full          = ∀{x y} → Surjective(map{x}{y})
    FullyFaithful = ∀{x y} → Bijective (map{x}{y})
    -- TODO: Conservative  = ∀{x y : Objₗ}{f : x ⟶ y} → Morphism.Isomorphism(\{x} → _∘_ {x = x})(\{x} → id{x = x})(map f) → Morphism.Isomorphism(\{x} → _∘_ {x = x})(id)(f)

module _
  ⦃ morphism-equiv : ∀{x y : Obj} → Equiv{ℓₑ}(Morphism x y) ⦄
  (Category : Category(Morphism))
  where

  Endofunctor = Functor(Category)(Category)
  module Endofunctor = Functor{Categoryₗ = Category}{Categoryᵣ = Category}

_→ᶠᵘⁿᶜᵗᵒʳ_ : CategoryObject{ℓₗₒ}{ℓₗₘ}{ℓₗₑ} → CategoryObject{ℓᵣₒ}{ℓᵣₘ}{ℓᵣₑ} → Type
catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ = ∃(Functor (CategoryObject.category(catₗ)) ((CategoryObject.category(catᵣ))))

⟲ᶠᵘⁿᶜᵗᵒʳ_ : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ} → Type
⟲ᶠᵘⁿᶜᵗᵒʳ cat = cat →ᶠᵘⁿᶜᵗᵒʳ cat
