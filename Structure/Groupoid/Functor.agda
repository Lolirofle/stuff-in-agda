module Structure.Groupoid.Functor where

open import Functional using (_on₂_)
open import Lang.Instance
import      Lvl
open import Logic.Predicate
open import Structure.Category
import      Structure.Category.Functor as Category
open import Structure.Function
open import Structure.Groupoid
import      Structure.Relator.Names as Names
open import Structure.Setoid.WithLvl
open import Syntax.Function
open import Type

private variable ℓ ℓₒ ℓₘ ℓₗₒ ℓₗₘ ℓᵣₒ ℓᵣₘ ℓₑ ℓₗₑ ℓᵣₑ : Lvl.Level
private variable Obj Objₗ Objᵣ : Type{ℓ}
private variable _⟶_ _⟶ₗ_ _⟶ᵣ_ : Objₗ → Objᵣ → Type{ℓ}

module _
  ⦃ morphism-equivₗ : ∀{x y : Objₗ} → Equiv{ℓₗₑ}(x ⟶ₗ y) ⦄
  ⦃ morphism-equivᵣ : ∀{x y : Objᵣ} → Equiv{ℓᵣₑ}(x ⟶ᵣ y) ⦄
  (Groupoidₗ : Groupoid(_⟶ₗ_))
  (Groupoidᵣ : Groupoid(_⟶ᵣ_))
  where

  -- A covariant functor.
  -- A mapping which transforms objects and morphisms from one category to another while "preserving" the groupoid structure.
  -- A homomorphism between groupoids.
  record Functor (F : Objₗ → Objᵣ) : Type{Lvl.of(Type.of(Groupoidₗ)) Lvl.⊔ Lvl.of(Type.of(Groupoidᵣ))} where
    constructor intro
    open Groupoid ⦃ … ⦄

    private instance _ = Groupoidₗ
    private instance _ = Groupoidᵣ

    field
      map : Names.Subrelation(_⟶ₗ_) ((_⟶ᵣ_) on₂ F)

    field
      ⦃ map-function ⦄     : ∀{x y} → Function(map{x}{y})
      ⦃ op-preserving ⦄    : ∀{x y z : Objₗ}{f : y ⟶ₗ z}{g : x ⟶ₗ y} → (map(f ∘ g) ≡ map(f) ∘ map(g))
      ⦃ inv-preserving ⦄   : ∀{x y : Objₗ}{f : x ⟶ₗ y} → (map(inv f) ≡ inv(map f))
      ⦃ id-preserving ⦄    : ∀{x : Objₗ} → (map(id {x = x}) ≡ id)

    categoryFunctor : Category.Functor(category ⦃ r = Groupoidₗ ⦄)(category ⦃ r = Groupoidᵣ ⦄) (F)
    Category.Functor.map           categoryFunctor = map
    Category.Functor.map-function  categoryFunctor = map-function
    Category.Functor.op-preserving categoryFunctor = op-preserving
    Category.Functor.id-preserving categoryFunctor = id-preserving
    open Category.Functor(categoryFunctor) public hiding (map ; map-function ; op-preserving ; id-preserving)

module _
  ⦃ morphism-equiv : ∀{x y : Obj} → Equiv{ℓₑ}(x ⟶ y) ⦄
  (Groupoid : Groupoid(_⟶_))
  where

  Endofunctor = Functor(Groupoid)(Groupoid)
  module Endofunctor = Functor{Groupoidₗ = Groupoid}{Groupoidᵣ = Groupoid}

_→ᶠᵘⁿᶜᵗᵒʳ_ : GroupoidObject{ℓₗₒ}{ℓₗₘ}{ℓₗₑ} → GroupoidObject{ℓᵣₒ}{ℓᵣₘ}{ℓᵣₑ} → Type
grpₗ →ᶠᵘⁿᶜᵗᵒʳ grpᵣ = ∃(Functor (GroupoidObject.groupoid(grpₗ)) ((GroupoidObject.groupoid(grpᵣ))))

⟲ᶠᵘⁿᶜᵗᵒʳ_ : GroupoidObject{ℓₒ}{ℓₘ}{ℓₑ} → Type
⟲ᶠᵘⁿᶜᵗᵒʳ grp = grp →ᶠᵘⁿᶜᵗᵒʳ grp
