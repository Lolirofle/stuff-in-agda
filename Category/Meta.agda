module Category.Meta where

import      Lvl
open import Data
open import Functional using (const) renaming (id to idf ; _∘_ to _∘f_)
open import Logic.Propositional
open import Logic.Predicate{Lvl.𝟎}
open import Relator.Equals{Lvl.𝟎}

-- The type of a morphism
Morphism : ∀{ℓₒ ℓₘ} → Set(ℓₒ) → Set(ℓₒ Lvl.⊔ (Lvl.𝐒 ℓₘ))
Morphism{_}{ℓₘ}(Obj) = (Obj → Obj → Set(ℓₘ))

-- Obj is the collection of objects
-- M   is the collection of morphisms
record Category {ℓₒ ℓₘ} (Obj : Set(ℓₒ)) (M : Morphism{ℓₒ}{ℓₘ}(Obj)) : Set(ℓₒ Lvl.⊔ ℓₘ) where
  field
    _∘_ : ∀{x y z : Obj} → (M y z) → (M x y) → (M x z)
    id  : ∀{x : Obj} → (M x x)

  field
    .identityₗ     : ∀{x y : Obj}{f : M x y} → (id ∘ f ≡ f)
    .identityᵣ     : ∀{x y : Obj}{f : M x y} → (f ∘ id ≡ f)
    .associativity : ∀{x y z W : Obj}{f : M y x}{g : M z y}{h : M W z} → (f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h)

  Isomorphism : ∀{x y} → (M x y) → Stmt
  Isomorphism(f) = ∃(g ↦ (g ∘ f ≡ id)∧(f ∘ g ≡ id))

  inv : ∀{x y} (f : M x y) → ⦃ _ : Isomorphism(f) ⦄ → (M y x)
  inv (_) ⦃ proof ⦄ = [∃]-extract(proof)

  inverseₗ : ∀{x y}{f : M x y} → ⦃ _ : Isomorphism(f) ⦄ → ((inv f) ∘ f ≡ id)
  inverseₗ ⦃ proof ⦄ = [∧]-elimₗ([∃]-property(proof))

  inverseᵣ : ∀{x y}{f : M x y} → ⦃ _ : Isomorphism(f) ⦄ → (f ∘ (inv f) ≡ id)
  inverseᵣ ⦃ proof ⦄ = [∧]-elimᵣ([∃]-property(proof))

  Isomorphic : Obj → Obj → Stmt
  Isomorphic(x)(y) = ∃(Isomorphism{x}{y})

EmptyCategory : ∀{ℓₒ ℓₘ} → Category{ℓₒ}{ℓₘ}(Empty)(empty)
Category._∘_           (EmptyCategory) {}
Category.id            (EmptyCategory) {}
Category.identityₗ     (EmptyCategory) {}
Category.identityᵣ     (EmptyCategory) {}
Category.associativity (EmptyCategory) {}

SingleCategory : ∀{ℓₒ ℓₘ} → Category{ℓₒ}{ℓₘ}(Unit)(const(const Unit))
Category._∘_           (SingleCategory) <> <> = <>
Category.id            (SingleCategory) = <>
Category.identityₗ     (SingleCategory) = [≡]-intro
Category.identityᵣ     (SingleCategory) = [≡]-intro
Category.associativity (SingleCategory) = [≡]-intro

SetCategory : ∀{ℓ} → Category(Set(ℓ))(x ↦ y ↦ (x → y))
Category._∘_           (SetCategory) = _∘f_
Category.id            (SetCategory) = idf
Category.identityₗ     (SetCategory) = [≡]-intro
Category.identityᵣ     (SetCategory) = [≡]-intro
Category.associativity (SetCategory) = [≡]-intro

-- "Preserves structure"
record CovariantFunctor
    {ℓₒ₁ ℓₘ₁ ℓₒ₂ ℓₘ₂}
    {Obj₁ : Set(ℓₒ₁)}
    {Obj₂ : Set(ℓₒ₂)}
    {M₁ : Obj₁ → Obj₁ → Set(ℓₘ₁)}
    {M₂ : Obj₂ → Obj₂ → Set(ℓₘ₂)}
    (F : Obj₁ → Obj₂)
    (Category₁ : Category Obj₁ M₁)
    (Category₂ : Category Obj₂ M₂)
  : Set((ℓₒ₁ Lvl.⊔ ℓₘ₁) Lvl.⊔ (ℓₒ₂ Lvl.⊔ ℓₘ₂)) where
  private
    _∘₁_ = Category._∘_ (Category₁)
    _∘₂_ = Category._∘_ (Category₂)

    id₁ = Category.id (Category₁)
    id₂ = Category.id (Category₂)

  field
    map : ∀{x y} → (M₁ x y) → (M₂(F x)(F y))

  field
    .[∘]-compatibility : ∀{x y z}{f : M₁ y z}{g : M₁ x y} → (map(f ∘₁ g) ≡ map(f) ∘₂ map(g))
    .id-compatibility  : ∀{x} → (map(id₁{x}) ≡ id₂)

{-
record Category (Obj : Set) (M : Set) : Set where
  field
    domain   : M → Obj
    codomain : M → Obj

  field
    composition : ∀{f g : M} → ⦃ _ : codomain(f) ≡ domain(g) ⦄ → ∃(h ↦ (domain(h) ≡ domain(f)) ∧ (codomain(h) ≡ codomain(g)))

  _∘_ : (g : M) → (f : M) → ⦃ _ : codomain(f) ≡ domain(g) ⦄ → M
  _∘_ g f ⦃ proof ⦄ = [∃]-extract(composition ⦃ proof ⦄)

  field
    identity      : ∃(id ↦ (domain(id) ≡ codomain(id)) ∧ (∀{f} → ⦃ _ : codomain(id) ≡ domain(f) ⦄ → (f ∘ id ≡ f)) ∧ (∀{f} → ⦃ _ : codomain(f) ≡ domain(id) ⦄ → (id ∘ f ≡ f)))
    associativity : ∀{f g h} → ⦃ _ : codomain(h) ≡ domain(g) ⦄ → ⦃ _ : codomain(g) ≡ domain(f) ⦄ → (f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h)
-}
