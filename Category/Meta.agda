module Category.Meta where -- TODO: Move to Structure

import      Lvl
open import Data
open import Functional using (const ; [↦]) renaming (id to idf ; _∘_ to _∘f_)
open import Logic.Propositional
open import Logic.Predicate{Lvl.𝟎}
open import Relator.Equals{Lvl.𝟎}
open import Relator.Equals.Theorems{Lvl.𝟎}
open import Structure.Relator.Properties{Lvl.𝟎}

-- The type of collections of morphisms
-- Could be seen as an generalization of functions.
Morphism : ∀{ℓₒ ℓₘ} → Set(ℓₒ) → Set(ℓₒ Lvl.⊔ (Lvl.𝐒 ℓₘ))
Morphism{_}{ℓₘ}(Obj) = (Obj → Obj → Set(ℓₘ))

-- Obj is the collection of objects.
-- M   is the collection of morphisms.
-- Could be seen as an generalization of a collection of sets and functions between them
-- because these are the algebraic rules that makes composition of functions useful.
record Category {ℓₒ ℓₘ} (Obj : Set(ℓₒ)) (M : Morphism{ℓₒ}{ℓₘ}(Obj)) : Set(ℓₒ Lvl.⊔ ℓₘ) where
  field
    -- Existence of morphisms constructed by connecting two morphisms (The composition of two morphisms).
    _∘_ : ∀{x y z : Obj} → (M y z) → (M x y) → (M x z)

    -- Existence of a morphism connected to itself (The identity morphism).
    id  : ∀{x : Obj} → (M x x)

  field
    ⦃ .identityₗ     ⦄ : ∀{x y : Obj}{f : M x y} → (id ∘ f ≡ f)
    ⦃ .identityᵣ     ⦄ : ∀{x y : Obj}{f : M x y} → (f ∘ id ≡ f)
    ⦃ .associativity ⦄ : ∀{x y z W : Obj}{f : M y x}{g : M z y}{h : M W z} → (f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h)

  -- A morphism is a isomorphism when there is an inverse of the morphism.
  Isomorphism : ∀{x y} → (M x y) → Stmt
  Isomorphism(f) = ∃(g ↦ (g ∘ f ≡ id)∧(f ∘ g ≡ id))

  -- The inverse of a morphism.
  inv : ∀{x y} (f : M x y) → ⦃ _ : Isomorphism(f) ⦄ → (M y x)
  inv (_) ⦃ proof ⦄ = [∃]-witness(proof)

  -- Proof that the inverse actually is an left inverse.
  inverseₗ : ∀{x y}{f : M x y} → ⦃ _ : Isomorphism(f) ⦄ → ((inv f) ∘ f ≡ id)
  inverseₗ ⦃ proof ⦄ = [∧]-elimₗ([∃]-proof(proof))

  -- Proof that the inverse actually is an right inverse.
  inverseᵣ : ∀{x y}{f : M x y} → ⦃ _ : Isomorphism(f) ⦄ → (f ∘ (inv f) ≡ id)
  inverseᵣ ⦃ proof ⦄ = [∧]-elimᵣ([∃]-proof(proof))

  -- Proposition stating that two objects are isomorphic.
  Isomorphic : Obj → Obj → Stmt
  Isomorphic(x)(y) = ∃(Isomorphism{x}{y})

-- The empty category is a category contaning nothing.
-- The objects are empty.
-- The morphisms are empty.
emptyCategory : ∀{ℓₒ ℓₘ} → Category{ℓₒ}{ℓₘ}(Empty)(empty)
Category._∘_           (emptyCategory) {}
Category.id            (emptyCategory) {}
Category.identityₗ     (emptyCategory) {}
Category.identityᵣ     (emptyCategory) {}
Category.associativity (emptyCategory) {}

-- The single category is a category contaning a single object.
-- The objects consists of a single thing.
-- The morphisms consists of a single connection connecting the single thing to itself.
singleCategory : ∀{ℓₒ ℓₘ} → Category{ℓₒ}{ℓₘ}(Unit)(const(const Unit))
Category._∘_           (singleCategory) <> <> = <>
Category.id            (singleCategory) = <>
Category.identityₗ     (singleCategory) = [≡]-intro
Category.identityᵣ     (singleCategory) = [≡]-intro
Category.associativity (singleCategory) = [≡]-intro

-- The set category is a category contaning all sets/types of a single level in the language.
-- The objects are all sets/types.
-- The morphisms are all functions where the domain/codomain-pair are from these objects.
setCategory : ∀{ℓ} → Category(Set(ℓ))(x ↦ y ↦ (x → y))
Category._∘_           (setCategory) = _∘f_
Category.id            (setCategory) = idf
Category.identityₗ     (setCategory) = [≡]-intro
Category.identityᵣ     (setCategory) = [≡]-intro
Category.associativity (setCategory) = [≡]-intro

module _ {ℓₒ₁}{ℓₘ₁} {ℓₒ₂}{ℓₘ₂} where
  -- A covariant functor.
  -- A morphism between categories.
  -- "Preserves structure"
  record Functor
      {Obj₁ : Set(ℓₒ₁)}
      {Obj₂ : Set(ℓₒ₂)}
      {M₁ : Obj₁ → Obj₁ → Set(ℓₘ₁)}
      {M₂ : Obj₂ → Obj₂ → Set(ℓₘ₂)}
      (F : Obj₁ → Obj₂)
      (Category₁ : Category Obj₁ M₁)
      (Category₂ : Category Obj₂ M₂)
    : Set((ℓₒ₁ Lvl.⊔ ℓₘ₁) Lvl.⊔ (ℓₒ₂ Lvl.⊔ ℓₘ₂))
    where
    _∘₁_ = Category._∘_ (Category₁)
    _∘₂_ = Category._∘_ (Category₂)

    id₁ = Category.id (Category₁)
    id₂ = Category.id (Category₂)

    field
      -- Morphs/Transforms morphisms from category 1 to category 2
      map : ∀{x y} → (M₁ x y) → (M₂(F x)(F y))

    field
      ⦃ .[∘]-preserving ⦄ : ∀{x y z}{f : M₁ y z}{g : M₁ x y} → (map(f ∘₁ g) ≡ map(f) ∘₂ map(g))
      ⦃ .id-preserving  ⦄ : ∀{x} → (map(id₁{x}) ≡ id₂)

    -- Morphs/Transforms objects from category 1 to category 2
    functor = F

    morphisms₁ = M₁
    morphisms₂ = M₂

    category₁ = Category₁
    category₂ = Category₂

module _ {ℓₒ}{ℓₘ} where
  constantFunctor : ∀{Obj₁}{Obj₂}{M₁}{M₂} → (obj₂ : Obj₂) → (cat₁ : _) → (cat₂ : _) → Functor{ℓₒ}{ℓₘ}{ℓₒ}{ℓₘ} {Obj₁}{Obj₂}{M₁}{M₂} (const(obj₂))(cat₁)(cat₂)
  Functor.map              (constantFunctor(obj₂) (_)(cat₂)) = const(Category.id(cat₂) {obj₂})
  Functor.[∘]-preserving(constantFunctor(obj₂) (_)(cat₂)) = symmetry (Category.identityₗ(cat₂))
  Functor.id-preserving (constantFunctor(obj₂) (_)(cat₂)) = [≡]-intro

module _ {ℓₒ}{ℓₘ} where
  -- A covariant functor from a category to itself
  EndoFunctor : ∀{Obj : Set(ℓₒ)} {M : Obj → Obj → Set(ℓₘ)} → (Obj → Obj) → Category(Obj)(M) → Set(ℓₒ Lvl.⊔ ℓₘ)
  EndoFunctor {Obj}{M} (F) (Category) = Functor {ℓₒ}{ℓₘ}{ℓₒ}{ℓₘ} {Obj}{Obj} {M}{M} (F) (Category)(Category)

  identityFunctor : ∀{Obj}{M} → (cat : _) → EndoFunctor{Obj}{M} (Functional.id)(cat)
  Functor.map              (identityFunctor(_)) = Functional.id
  Functor.[∘]-preserving(identityFunctor(_)) = [≡]-intro
  Functor.id-preserving (identityFunctor(_)) = [≡]-intro

{-
record Category (Obj : Set) (M : Set) : Set where
  field
    domain   : M → Obj
    codomain : M → Obj

  field
    composition : ∀{f g : M} → ⦃ _ : codomain(f) ≡ domain(g) ⦄ → ∃(h ↦ (domain(h) ≡ domain(f)) ∧ (codomain(h) ≡ codomain(g)))

  _∘_ : (g : M) → (f : M) → ⦃ _ : codomain(f) ≡ domain(g) ⦄ → M
  _∘_ g f ⦃ proof ⦄ = [∃]-witness(composition ⦃ proof ⦄)

  field
    identity      : ∃(id ↦ (domain(id) ≡ codomain(id)) ∧ (∀{f} → ⦃ _ : codomain(id) ≡ domain(f) ⦄ → (f ∘ id ≡ f)) ∧ (∀{f} → ⦃ _ : codomain(f) ≡ domain(id) ⦄ → (id ∘ f ≡ f)))
    associativity : ∀{f g h} → ⦃ _ : codomain(h) ≡ domain(g) ⦄ → ⦃ _ : codomain(g) ≡ domain(f) ⦄ → (f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h)
-}
