module Structure.Category.Functor where

open import Lang.Instance
import      Lvl
open import Logic.Predicate
open import Sets.Setoid
open import Structure.Category
open import Structure.Function
open import Type

private variable ℓ : Lvl.Level
private variable Obj Objₗ Objᵣ : Type{ℓ}
private variable Morphism Morphismₗ Morphismᵣ : Objₗ → Objᵣ → Type{ℓ}

module _
  ⦃ morphism-equivₗ : ∀{x y : Objₗ} → Equiv(Morphismₗ x y) ⦄
  ⦃ morphism-equivᵣ : ∀{x y : Objᵣ} → Equiv(Morphismᵣ x y) ⦄
  (Categoryₗ : Category(Morphismₗ))
  (Categoryᵣ : Category(Morphismᵣ))
  where

  -- A covariant functor.
  -- A homomorphism between categories.
  -- "Preserves structure".
  -- A "functor" is specifically a function which morphs/transforms objects from the left category to the right category.
  record Functor (F : Objₗ → Objᵣ) : Type{Lvl.of(type-of(Categoryₗ)) Lvl.⊔ Lvl.of(type-of(Categoryᵣ))} where
    open Category ⦃ … ⦄
    open Category.ArrowNotation ⦃ … ⦄
    private instance _ = Categoryₗ
    private instance _ = Categoryᵣ

    field
      -- Morphs/Transforms morphisms from the left category to the right category.
      map : ∀{x y : Objₗ} → (x ⟶ y) → (F(x) ⟶ F(y))

    field
      ⦃ map-function ⦄     : ∀{x y} → Function(map{x}{y})
      ⦃ op-preserving ⦄    : ∀{x y z : Objₗ}{f : y ⟶ z}{g : x ⟶ y} → (map(f ∘ g) ≡ map(f) ∘ map(g))
      ⦃ id-preserving ⦄    : ∀{x : Objₗ} → (map(id {x = x}) ≡ id)

    open import Structure.Category.Properties
    open import Structure.Function.Domain

    Faithful      = ∀{x y} → Injective (map{x}{y})
    Full          = ∀{x y} → Surjective(map{x}{y})
    FullyFaithful = ∀{x y} → Bijective (map{x}{y})
    -- TODO: Conservative  = ∀{x y : Objₗ}{f : x ⟶ y} → Morphism.Isomorphism(\{x} → _∘_ {x = x})(\{x} → id{x = x})(map f) → Morphism.Isomorphism(\{x} → _∘_ {x = x})(id)(f)

  _→ᶠᵘⁿᶜᵗᵒʳ_ = ∃(Functor)

module _
  ⦃ morphism-equiv : ∀{x y : Obj} → Equiv(Morphism x y) ⦄
  (Category : Category(Morphism))
  where

  Endofunctor = Functor(Category)(Category)
  module Endofunctor = Functor{Categoryₗ = Category}{Categoryᵣ = Category}

  ⟲ᶠᵘⁿᶜᵗᵒʳ = ∃(Endofunctor)
