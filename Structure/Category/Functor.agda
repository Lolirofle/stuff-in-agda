module Structure.Category.Functor where

import      Lvl
open import Logic.Predicate
open import Sets.Setoid
open import Structure.Category

module _
  {ℓₒₗ ℓₘₗ ℓₒᵣ ℓₘᵣ : Lvl.Level}
  {Objₗ : Set(ℓₒₗ)}
  {Objᵣ : Set(ℓₒᵣ)}
  {Morphismₗ : Objₗ → Objₗ → Set(ℓₘₗ)}
  ⦃ morphism-equivₗ : ∀{x y} → Equiv(Morphismₗ x y) ⦄
  {Morphismᵣ : Objᵣ → Objᵣ → Set(ℓₘᵣ)}
  ⦃ morphism-equivᵣ : ∀{x y} → Equiv(Morphismᵣ x y) ⦄
  (Categoryₗ : Category(Morphismₗ))
  (Categoryᵣ : Category(Morphismᵣ))
  where

  -- Arrow notation for the domain category and the codomain category of a functor.
  module SideNotation where
    _⟶ₗ_ = Morphismₗ
    _⟶ᵣ_ = Morphismᵣ

    _∘ₗ_ = Category._∘_ (Categoryₗ)
    _∘ᵣ_ = Category._∘_ (Categoryᵣ)

    idₗ = Category.id (Categoryₗ)
    idᵣ = Category.id (Categoryᵣ)

  -- A covariant functor.
  -- A homomorphism between categories.
  -- "Preserves structure"
  -- A "functor" is specifically a function which morphs/transforms objects from category 1 to category 2.
  record Functor (F : Objₗ → Objᵣ) : Set((ℓₒₗ Lvl.⊔ ℓₘₗ) Lvl.⊔ (ℓₒᵣ Lvl.⊔ ℓₘᵣ)) where
    open SideNotation

    field
      -- Morphs/Transforms morphisms from category 1 to category 2
      map : ∀{x y} → (x ⟶ₗ y) → (F(x) ⟶ᵣ F(y))

    field
      ⦃ op-preserving ⦄ : ∀{x y z}{f : y ⟶ₗ z}{g : x ⟶ₗ y} → (map(f ∘ₗ g) ≡ map(f) ∘ᵣ map(g))
      ⦃ id-preserving  ⦄ : ∀{x} → (map(idₗ{x}) ≡ idᵣ)

  _→ᶠᵘⁿᶜᵗᵒʳ_ = ∃(Functor)

module _
  {ℓₒ ℓₘ : Lvl.Level}
  {Obj : Set(ℓₒ)}
  {Morphism : Obj → Obj → Set(ℓₘ)}
  ⦃ morphism-equiv : ∀{x y} → Equiv(Morphism x y) ⦄
  (Category : Category(Morphism))
  where

  Endofunctor = Functor(Category)(Category)
