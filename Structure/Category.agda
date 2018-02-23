module Structure.Category where

import      Lvl
open import Data
open import Functional using (const ; [↦] ; _→ᶠ_) renaming (id to idf ; _∘_ to _∘f_)
open import Logic.Propositional
open import Logic.Predicate{Lvl.𝟎}
import      Relator.Equals
open import Relator.Equals.Theorems{Lvl.𝟎}
open import Structure.Relator.Properties{Lvl.𝟎}

{- TODO:
Usually, a homomorphism is a function which have the following property:
  For a function f: A → B, and two operations (▫ᴬ): A² → A, (▫ᴮ): B² → B
  (f is a homomorphism) ⇔ (∀(a₁∊A)∀(a₂∊A). f(a₁ ▫ᴬ a₂) = f(a₁) ▫ᴮ f(a₂))
Or maybe more generally:
  For a function f: A → B, a whole number n, and two operations ga: Aⁿ → A, gb: Bⁿ → B
  (f is a homomorphism) ⇔ (∀(a∊Aⁿ). f(ga(a)) = gb(map f(a)))
But what is it called in "Category theory"?
Is the following what usually is called a "homomorphism"?
  https://en.wikipedia.org/wiki/Natural_transformation
-}

module _ {ℓₒ ℓₘ : Lvl.Level} where
  open Relator.Equals{ℓₘ}

  -- The type of collections of morphisms
  -- Could be seen as an generalization of functions.
  Morphism : Set(ℓₒ) → Set(ℓₒ Lvl.⊔ (Lvl.𝐒 ℓₘ))
  Morphism(Obj) = (Obj → Obj → Set(ℓₘ))

  -- A type and a binary relation using this type is a category when:
  -- • The relator is transitive.
  -- • The relator is reflexive.
  -- • A proof of transitivty with a proof of reflexivity is unique.
  -- • Chains of proofs of transitivty in any direction are the same.
  --
  -- Could be seen as an generalization of a collection of sets and functions between them
  -- because these are the algebraic rules that makes composition of functions useful.
  -- In this special case, the relator describes the existence of a function between two sets.
  --
  -- When the objects are algebraic structures (or categories themselves), (TODO: Probably separate cases)
  -- then the morphisms are functors, and are usually called homomorphisms. (TODO: But maybe not. Homomorphisms is usually defined with not having the property of`id-preserving`: https://math.stackexchange.com/questions/405459/homomorphisms-vs-functors/405479#comment867772_405459 https://ncatlab.org/nlab/show/homomorphism)
  --
  -- Obj is the collection of objects.
  -- M   is the collection of morphisms.
  record Category {Obj : Set(ℓₒ)} (M : Morphism(Obj)) : Set(ℓₒ Lvl.⊔ ℓₘ) where -- TODO: A category could also be seen as an algebraic structure, but one difference from e.g. groups is that this definition also tries to generalize the notion of functions as elements of the algebraic structure
    field
      -- Existence of morphisms constructed by connecting two morphisms (The composition of two morphisms).
      -- Existence of a binary operator on morphisms connecting the ends of two morphisms.
      -- Proof of transitivity for the binary relator M.
      _∘_ : ∀{x y z : Obj} → (M y z) → (M x y) → (M x z) -- TODO: Note that this is the operator like the operators in other algebraic structures with binary operators

      -- Existence of a morphism connected to itself (The identity morphism).
      -- Proof of reflexivity for the binary relator M.
      id  : ∀{x : Obj} → (M x x)

    field
      -- The morphism `id` behaves like a left identity element with respect to the binary operator.
      -- Applying the proof of reflexivity on transitivity to the left is an identity function for proofs.
      ⦃ .identityₗ ⦄ : ∀{x y : Obj}{f : M x y} → (id ∘ f ≡ f)

      -- The morphism `id` behaves like a right identity element with respect to the binary operator.
      -- Applying the proof of reflexivity on transitivity to the right is an identity function for proofs.
      ⦃ .identityᵣ ⦄ : ∀{x y : Obj}{f : M x y} → (f ∘ id ≡ f)

      -- The binary operator on mophisms is associative.
      -- The order of applying two transitiviies on three proofs does not matter. It it the same proof.
      ⦃ .associativity ⦄ : ∀{x y z W : Obj}{f : M y x}{g : M z y}{h : M W z} → ((f ∘ g) ∘ h ≡ f ∘ (g ∘ h))

    -- A morphism is an isomorphism when it is bijective (there is an inverse of the morphism with respect to the operator).
    Isomorphism : ∀{x y} → (M x y) → Stmt
    Isomorphism(f) = ∃(g ↦ (g ∘ f ≡ id)∧(f ∘ g ≡ id))

    -- A morphism is an endomorphism when the domain equals the codomain.
    Endomorphism : ∀{x y} → (M x y) → Stmt
    Endomorphism{x}{y}(_) = (x ≡ y)

    -- A morphism is an endomorphism and an isomorphism.
    Automorphism : ∀{x y} → (M x y) → Stmt
    Automorphism(f) = (Isomorphism(f) ∧ Endomorphism(f))

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

  -- The empty category is a category containing nothing.
  -- The objects are empty.
  -- The morphisms are empty.
  emptyCategory : Category{Empty}(empty)
  Category._∘_           (emptyCategory) {}
  Category.id            (emptyCategory) {}
  Category.identityₗ     (emptyCategory) {}
  Category.identityᵣ     (emptyCategory) {}
  Category.associativity (emptyCategory) {}

  -- The single category is a category containing a single object.
  -- The objects consists of a single thing.
  -- The morphisms consists of a single connection connecting the single thing to itself.
  singleCategory : Category{Unit}(const(const Unit))
  Category._∘_           (singleCategory) <> <> = <>
  Category.id            (singleCategory) = <>
  Category.identityₗ     (singleCategory) = [≡]-intro
  Category.identityᵣ     (singleCategory) = [≡]-intro
  Category.associativity (singleCategory) = [≡]-intro

module _ {ℓ} where
  open Relator.Equals{ℓ}

  -- The set category is a category containing all sets/types of a single level in the language.
  -- The objects are all sets/types.
  -- The morphisms are all functions where the domain/codomain-pair are from these objects.
  setCategory : Category{_}{_}{Set(ℓ)}(_→ᶠ_)
  Category._∘_           (setCategory) = _∘f_
  Category.id            (setCategory) = idf
  Category.identityₗ     (setCategory) = [≡]-intro
  Category.identityᵣ     (setCategory) = [≡]-intro
  Category.associativity (setCategory) = [≡]-intro

module _ {ℓₒ₁ ℓₘ₁ ℓₒ₂ ℓₘ₂ : Lvl.Level} where
  open Relator.Equals{ℓₘ₂}

  -- A covariant functor.
  -- A morphism between categories.
  -- "Preserves structure"
  record Functor
      {Obj₁ : Set(ℓₒ₁)}
      {Obj₂ : Set(ℓₒ₂)}
      {M₁ : Obj₁ → Obj₁ → Set(ℓₘ₁)}
      {M₂ : Obj₂ → Obj₂ → Set(ℓₘ₂)}
      (F : Obj₁ → Obj₂)
      (Category₁ : Category {_}{_} {Obj₁} M₁)
      (Category₂ : Category {_}{_} {Obj₂} M₂)
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

  constantFunctor : ∀{Obj₁}{Obj₂}{M₁}{M₂} → (obj₂ : Obj₂) → (cat₁ : _) → (cat₂ : _) → Functor{Obj₁}{Obj₂}{M₁}{M₂} (const(obj₂))(cat₁)(cat₂)
  Functor.map           (constantFunctor(obj₂) (_)(cat₂)) = const(Category.id(cat₂) {obj₂})
  Functor.[∘]-preserving(constantFunctor(obj₂) (_)(cat₂)) = symmetry (Category.identityₗ(cat₂))
  Functor.id-preserving (constantFunctor(obj₂) (_)(cat₂)) = [≡]-intro

{- module _ {ℓₒ₁}{ℓₘ₁} {ℓₒ₂}{ℓₘ₂} {ℓₒ₃}{ℓₘ₃} where
  compositionFunctor : ∀{Obj₁}{Obj₂}{Obj₃} {M₁}{M₂}{M₃} {cat₁}{cat₂}{cat₃} {F₁₂}{F₂₃}
                               → Functor{ℓₒ₂}{ℓₘ₂} {ℓₒ₃}{ℓₘ₃} {Obj₂}{Obj₃}{M₂}{M₃} (F₂₃)(cat₂)(cat₃)
                               → Functor{ℓₒ₁}{ℓₘ₁} {ℓₒ₂}{ℓₘ₂} {Obj₁}{Obj₂}{M₁}{M₂} (F₁₂)(cat₁)(cat₂)
                               → Functor{ℓₒ₁}{ℓₘ₁} {ℓₒ₃}{ℓₘ₃} {Obj₁}{Obj₃}{M₁}{M₃} (F₂₃ ∘f F₁₂)(cat₁)(cat₃)
  Functor.map           (compositionFunctor (functor₂₃)(functor₁₂)){x}{y} = (Functor.map(functor₂₃){Functor.functor(functor₁₂)(x)}{Functor.functor(functor₁₂)(y)}) ∘f (Functor.map(functor₁₂){x}{y})
  Functor.[∘]-preserving(compositionFunctor (functor₂₃)(functor₁₂)) =
    ([≡]-with(expr ↦ Functor.map(functor₂₃)(expr))
      (Functor.[∘]-preserving(functor₁₂))
    )
    🝖 (Functor.[∘]-preserving(functor₂₃))
  Functor.id-preserving (compositionFunctor (functor₂₃)(functor₁₂)) =
    ([≡]-with(expr ↦ Functor.map(functor₂₃)(expr))
      (Functor.id-preserving(functor₁₂))
    )
    🝖 (Functor.id-preserving(functor₂₃))
  -- • {
  --     map₁₂(f ∘₁ g) ≡ map₁₂(f) ∘₂ map₁₂(g)
  --     map₂₃(map₁₂(f ∘₁ g)) ≡ map₂₃(map₁₂(f) ∘₂ map₁₂(g))
  -- }
  -- • map₂₃(f ∘₂ g) ≡ map₂₃(f) ∘₃ map₂₃(g)
  -- ⇒ map₂₃(map₁₂(f ∘₁ g)) ≡ map₂₃(map₁₂(f)) ∘₂ map₂₃(map₁₂(g))
-}

module _ {ℓₒ ℓₘ} where
  open Relator.Equals

  -- A covariant functor from a category to itself
  EndoFunctor : ∀{Obj : Set(ℓₒ)} {M : Obj → Obj → Set(ℓₘ)} → (Obj → Obj) → Category{_}{_} {Obj}(M) → Set(ℓₒ Lvl.⊔ ℓₘ)
  EndoFunctor {Obj}{M} (F) (Category) = Functor {ℓₒ}{ℓₘ}{ℓₒ}{ℓₘ} {Obj}{Obj} {M}{M} (F) (Category)(Category)

  identityFunctor : ∀{Obj}{M} → (cat : _) → EndoFunctor{Obj}{M} (Functional.id)(cat)
  Functor.map           (identityFunctor(_)) = Functional.id
  Functor.[∘]-preserving(identityFunctor(_)) = [≡]-intro
  Functor.id-preserving (identityFunctor(_)) = [≡]-intro

{-
categoryCategory : ∀{ℓ} → Category(Category(F))(Functor)
Category._∘_           (categoryCategory) = compositionFunctor
Category.id            (categoryCategory) = identityFunctor
Category.identityₗ     (categoryCategory) = [≡]-intro
Category.identityᵣ     (categoryCategory) = [≡]-intro
Category.associativity (categoryCategory) = [≡]-intro
-}

module _ {ℓ} where
  open import Structure.Operator.Monoid{Lvl.𝟎}{ℓ}

  monoidCategory : ∀{T : Set(ℓ)}{_▫_ : T → T → T} → Monoid{T}(_▫_) → Category{Lvl.𝟎}{ℓ} {Unit}(\_ → \_ → T)
  Category._∘_           (monoidCategory{_}{_▫_}(M)) {_}{_}{_} = (_▫_)
  Category.id            (monoidCategory{_}{_▫_}(M)) {_} = Monoid.id(M)
  Category.identityₗ     (monoidCategory{_}{_▫_}(M)) {_}{_} = Monoid.identityₗ(M)
  Category.identityᵣ     (monoidCategory{_}{_▫_}(M)) {_}{_} = Monoid.identityᵣ(M)
  Category.associativity (monoidCategory{_}{_▫_}(M)) {_}{_}{_}{_} = Monoid.associativity(M)
