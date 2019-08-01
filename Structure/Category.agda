module Structure.Category where

import      Lvl
open import Data
import      Data.Tuple as Tuple
import      Data.Tuple.Proofs
open        Tuple using (_,_)
open import Functional using (const ; [↦] ; _→ᶠ_) renaming (id to idf ; _∘_ to _∘f_)
open import Logic.Propositional
open import Logic.Predicate{Lvl.𝟎}
import      Relator.Equals
open import Relator.Equals.Proofs{Lvl.𝟎}
import      Relator.Equals.Uniqueness
open import Structure.Relator.Properties{Lvl.𝟎}
open import Type

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
  open Relator.Equals.Uniqueness{Lvl.𝟎}{ℓₘ}{ℓₘ} -- TODO: No ℓₒ?

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
  -- then the morphisms are functors, and are usually called homomorphisms. (TODO: But maybe not. A homomorphism is usually defined with not having the property of`id-preserving`: https://math.stackexchange.com/questions/405459/homomorphisms-vs-functors/405479#comment867772_405459 https://ncatlab.org/nlab/show/homomorphism)
  --
  -- Obj is the collection of objects.
  -- _⟶_ is the collection of morphisms.
  record Category {Obj : Set(ℓₒ)} (_⟶_ : Morphism(Obj)) : Set(ℓₒ Lvl.⊔ ℓₘ) where -- TODO: A category could also be seen as an algebraic structure, but one difference from e.g. groups is that this definition also tries to generalize the notion of functions as elements of the algebraic structure
    field
      -- Existence of morphisms constructed by connecting two morphisms (The composition of two morphisms).
      -- Existence of a binary operator on morphisms connecting the ends of two morphisms.
      -- Proof of transitivity for the binary relator (_⟶_).
      _∘_ : ∀{x y z : Obj} → (y ⟶ z) → (x ⟶ y) → (x ⟶ z) -- TODO: Note that this is the operator like the operators in other algebraic structures with binary operators

      -- Existence of a morphism connected to itself (The identity morphism).
      -- Proof of reflexivity for the binary relator (_⟶_).
      id  : ∀{x : Obj} → (x ⟶ x)

    field
      -- The morphism `id` behaves like a left identity element with respect to the binary operator.
      -- Applying the proof of reflexivity on transitivity to the left is an identity function for proofs.
      ⦃ .identityₗ ⦄ : ∀{x y : Obj}{f : x ⟶ y} → (id ∘ f ≡ f)

      -- The morphism `id` behaves like a right identity element with respect to the binary operator.
      -- Applying the proof of reflexivity on transitivity to the right is an identity function for proofs.
      ⦃ .identityᵣ ⦄ : ∀{x y : Obj}{f : x ⟶ y} → (f ∘ id ≡ f)

      -- The binary operator on mophisms is associative.
      -- The order of applying two transitivies on three proofs does not matter. It is the same proof.
      ⦃ .associativity ⦄ : ∀{x y z w : Obj}{f : y ⟶ x}{g : z ⟶ y}{h : w ⟶ z} → ((f ∘ g) ∘ h ≡ f ∘ (g ∘ h))

    -- The domain of a morphism
    dom : ∀{x y : Obj} → (x ⟶ y) → Obj
    dom{x}{y} (f) = x

    -- The codomain of a morphism
    codom : ∀{x y : Obj} → (x ⟶ y) → Obj
    codom{x}{y} (f) = y

    -- Reversed arrow
    converse : Morphism(Obj)
    converse y x = x ⟶ y
    private
      _⟵_ : Morphism(Obj)
      _⟵_ = converse

    -- A morphism is an isomorphism when it is bijective (there is an inverse of the morphism with respect to the operator).
    Isomorphism : ∀{x y} → (x ⟶ y) → Stmt
    Isomorphism(f) = ∃(g ↦ (g ∘ f ≡ id)∧(f ∘ g ≡ id))

    -- A morphism is an endomorphism when the domain and the codomain are equal.
    Endomorphism : ∀{x y} → (x ⟶ y) → Stmt
    Endomorphism{x}{y}(_) = (x ≡ y)

    -- A morphism is an automorphism when it is an endomorphism and an isomorphism.
    Automorphism : ∀{x} → (x ⟶ x) → Stmt
    Automorphism = Isomorphism
    -- Automorphism : ∀{x y} → (x ⟶ y) → Stmt
    -- Automorphism(f) = (Isomorphism(f) ∧ Endomorphism(f))

    -- A morphism is an monomorphism when it is left-cancellable ("injective").
    Monomorphism : ∀{x y} → (x ⟶ y) → Stmt
    Monomorphism{x} (f) = (∀{z}{g₁ g₂ : z ⟶ x} → (f ∘ g₁ ≡ f ∘ g₂) → (g₁ ≡ g₂))

    -- A morphism is an epimorphism when it is right-cancellable ("surjective").
    Epimorphism : ∀{x y} → (x ⟶ y) → Stmt
    Epimorphism{_}{y} (f) = (∀{z}{g₁ g₂ : y ⟶ z} → (g₁ ∘ f ≡ g₂ ∘ f) → (g₁ ≡ g₂))

    -- The inverse of a morphism.
    inv : ∀{x y} (f : x ⟶ y) → ⦃ _ : Isomorphism(f) ⦄ → (y ⟶ x)
    inv (_) ⦃ proof ⦄ = [∃]-witness(proof)

    -- Proof that the inverse actually is a left inverse.
    inverseₗ : ∀{x y}{f : x ⟶ y} → ⦃ _ : Isomorphism(f) ⦄ → ((inv f) ∘ f ≡ id)
    inverseₗ ⦃ proof ⦄ = [∧]-elimₗ([∃]-proof(proof))

    -- Proof that the inverse actually is a right inverse.
    inverseᵣ : ∀{x y}{f : x ⟶ y} → ⦃ _ : Isomorphism(f) ⦄ → (f ∘ (inv f) ≡ id)
    inverseᵣ ⦃ proof ⦄ = [∧]-elimᵣ([∃]-proof(proof))

    -- Proposition stating that two objects are isomorphic.
    Isomorphic : Obj → Obj → Stmt
    Isomorphic(x)(y) = ∃(Isomorphism{x}{y})

    -- An initial object is an object in which there is an unique morphism from it to every object.
    InitialObject : Obj → Stmt
    InitialObject(x) = (∀{y} → ∃!{x ⟶ y}(const ⊤))

    -- An terminal object is an object in which there is an unique morphism to it from every object.
    TerminalObject : Obj → Stmt
    TerminalObject(y) = (∀{x} → ∃!{x ⟶ y}(const ⊤))

    -- The opposite/dual category of a category.
    opposite : Category {Obj} (_⟵_)
    opposite = record{
        _∘_ = Functional.swap _∘_ ; -- \{x}{y}{z} yz xy → _∘_ {z}{y}{x} xy yz
        id = id ;

        identityₗ = identityᵣ ;
        identityᵣ = identityₗ ;
        associativity = \{x}{y}{z}{w} {f}{g}{h} → symmetry(associativity{w}{z}{y}{x} {h}{g}{f})
      }

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

module Product
  {ℓₒ ℓₘ : Lvl.Level}
  {Obj₁ : Set(ℓₒ)}
  {Obj₂ : Set(ℓₒ)}
  {_⟶₁_ : Obj₁ → Obj₁ → Set(ℓₘ)}
  {_⟶₂_ : Obj₂ → Obj₂ → Set(ℓₘ)}
  where

  open Category
  open Data.Tuple.Proofs
  open Relator.Equals{ℓₘ}

  [⨯]-obj : Set(ℓₒ)
  [⨯]-obj = Tuple._⨯_ Obj₁ Obj₂

  [⨯]-morphism : [⨯]-obj → [⨯]-obj → Set(ℓₘ)
  [⨯]-morphism(x₁ , x₂) (y₁ , y₂) = Tuple._⨯_ (x₁ ⟶₁ y₁) (x₂ ⟶₂ y₂)

  _⨯_ : Category(_⟶₁_) → Category(_⟶₂_) → Category{_}{_} {[⨯]-obj} [⨯]-morphism
  _∘_ (_⨯_ cat₁ cat₂) {x₁ , x₂}{y₁ , y₂}{z₁ , z₂} (yz₁ , yz₂) (xy₁ , xy₂) = (_∘_ cat₁ yz₁ xy₁ , _∘_ cat₂ yz₂ xy₂)
  id  (_⨯_ cat₁ cat₂) {x₁ , x₂} = (id cat₁ {x₁} , id cat₂ {x₂})
  identityₗ (_⨯_ cat₁ cat₂) {x₁ , x₂}{y₁ , y₂} {f₁ , f₂} = Tuple-equality (identityₗ cat₁ {x₁}{y₁} {f₁}) (identityₗ cat₂ {x₂}{y₂} {f₂})
  identityᵣ (_⨯_ cat₁ cat₂) {x₁ , x₂}{y₁ , y₂} {f₁ , f₂} = Tuple-equality (identityᵣ cat₁ {x₁}{y₁} {f₁}) (identityᵣ cat₂ {x₂}{y₂} {f₂})
  associativity (_⨯_ cat₁ cat₂) {x₁ , x₂}{y₁ , y₂}{z₁ , z₂}{w₁ , w₂} {f₁ , f₂}{g₁ , g₂}{h₁ , h₂} = Tuple-equality (associativity cat₁ {x₁}{y₁}{z₁}{w₁} {f₁}{g₁}{h₁}) (associativity cat₂ {x₂}{y₂}{z₂}{w₂} {f₂}{g₂}{h₂})

module _
  {ℓₒ₁ ℓₘ₁ ℓₒ₂ ℓₘ₂ : Lvl.Level}
  {Obj₁ : Set(ℓₒ₁)}
  {Obj₂ : Set(ℓₒ₂)}
  {_⟶₁_ : Obj₁ → Obj₁ → Set(ℓₘ₁)}
  {_⟶₂_ : Obj₂ → Obj₂ → Set(ℓₘ₂)}
  where

  open Relator.Equals{ℓₘ₂}

  -- A covariant functor.
  -- A morphism between categories.
  -- "Preserves structure"
  record Functor
      (Category₁ : Category {_}{_} {Obj₁} _⟶₁_)
      (Category₂ : Category {_}{_} {Obj₂} _⟶₂_)
    : Set((ℓₒ₁ Lvl.⊔ ℓₘ₁) Lvl.⊔ (ℓₒ₂ Lvl.⊔ ℓₘ₂))
    where

    private
      _∘₁_ = Category._∘_ (Category₁)
      _∘₂_ = Category._∘_ (Category₂)

      id₁ = Category.id (Category₁)
      id₂ = Category.id (Category₂)

    field
      -- Morphs/Transforms objects from category 1 to category 2
      functor : Obj₁ → Obj₂

      -- Morphs/Transforms morphisms from category 1 to category 2
      map : ∀{x y} → (x ⟶₁ y) → (functor(x) ⟶₂ functor(y))

    field
     ⦃ .[∘]-preserving ⦄ : ∀{x y z}{f : y ⟶₁ z}{g : x ⟶₁ y} → (map(f ∘₁ g) ≡ map(f) ∘₂ map(g))
     ⦃ .id-preserving  ⦄ : ∀{x} → (map(id₁{x}) ≡ id₂)

    .isomorphism-preserving : ∀{x y}{f : x ⟶₁ y} → Category.Isomorphism(Category₁)(f) → Category.Isomorphism(Category₂)(map f)
    isomorphism-preserving {x}{y} {f} ([∃]-intro g ⦃ [∧]-intro gfid fgid ⦄) = [∃]-intro (map g) ⦃ [∧]-intro proofₗ proofᵣ ⦄ where
      .proofₗ : map(g) ∘₂ map(f) ≡ id₂
      proofₗ =
        (symmetry [∘]-preserving :of: (map(g) ∘₂ map(f) ≡ map(g ∘₁ f)))
        🝖 ([≡]-with(map) gfid    :of: (_                ≡ map(id₁)))
        🝖 (id-preserving         :of: (_                ≡ id₂))

      .proofᵣ : map(f) ∘₂ map(g) ≡ id₂
      proofᵣ =
        (symmetry [∘]-preserving :of: (map(f) ∘₂ map(g) ≡ map(f ∘₁ g)))
        🝖 ([≡]-with(map) fgid    :of: (_                ≡ map(id₁)))
        🝖 (id-preserving         :of: (_                ≡ id₂))

  constantFunctor : (obj₂ : Obj₂) → (cat₁ : _) → (cat₂ : _) → Functor(cat₁)(cat₂)
  Functor.functor       (constantFunctor(obj₂) (_)(cat₂)) = const(obj₂)
  Functor.map           (constantFunctor(obj₂) (_)(cat₂)) = const(Category.id(cat₂) {obj₂})
  Functor.[∘]-preserving(constantFunctor(obj₂) (_)(cat₂)) = symmetry (Category.identityₗ(cat₂))
  Functor.id-preserving (constantFunctor(obj₂) (_)(cat₂)) = [≡]-intro

module _ {ℓₒ ℓₘ : Lvl.Level} where -- TODO: Level problems. Probably in the proofs {ℓₒ₁}{ℓₘ₁} {ℓₒ₂}{ℓₘ₂} {ℓₒ₃}{ℓₘ₃}
  private
    ℓₒ₁ = ℓₒ
    ℓₘ₁ = ℓₘ
    ℓₒ₂ = ℓₒ
    ℓₘ₂ = ℓₘ
    ℓₒ₃ = ℓₒ
    ℓₘ₃ = ℓₘ

  compositionFunctor : ∀{Obj₁}{Obj₂}{Obj₃} {M₁}{M₂}{M₃} {cat₁}{cat₂}{cat₃}
                     → Functor{ℓₒ₂}{ℓₘ₂} {ℓₒ₃}{ℓₘ₃} {Obj₂}{Obj₃}{M₂}{M₃} (cat₂)(cat₃)
                     → Functor{ℓₒ₁}{ℓₘ₁} {ℓₒ₂}{ℓₘ₂} {Obj₁}{Obj₂}{M₁}{M₂} (cat₁)(cat₂)
                     → Functor{ℓₒ₁}{ℓₘ₁} {ℓₒ₃}{ℓₘ₃} {Obj₁}{Obj₃}{M₁}{M₃} (cat₁)(cat₃)
  Functor.functor       (compositionFunctor (functor₂₃)(functor₁₂)) = Functor.functor(functor₂₃) ∘f Functor.functor(functor₁₂)
  Functor.map           (compositionFunctor (functor₂₃)(functor₁₂)){x}{y} = (Functor.map(functor₂₃){Functor.functor(functor₁₂)(x)}{Functor.functor(functor₁₂)(y)}) ∘f (Functor.map(functor₁₂){x}{y})
  Functor.[∘]-preserving(compositionFunctor (functor₂₃)(functor₁₂)) =
    ([≡]-with(Functor.map(functor₂₃))
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


module _ {ℓₒ ℓₘ} where
  open Relator.Equals

  -- A covariant functor from a category to itself
  EndoFunctor : ∀{Obj : Set(ℓₒ)} {_⟶_ : Obj → Obj → Set(ℓₘ)} → Category{_}{_} {Obj}(_⟶_) → Set(ℓₒ Lvl.⊔ ℓₘ)
  EndoFunctor {Obj}{_⟶_} (Category) = Functor {ℓₒ}{ℓₘ}{ℓₒ}{ℓₘ} {Obj}{Obj} {_⟶_}{_⟶_} (Category)(Category)

  identityFunctor : ∀{Obj}{_⟶_} → (cat : _) → EndoFunctor{Obj}{_⟶_} (cat)
  Functor.functor       (identityFunctor(_)) = Functional.id
  Functor.map           (identityFunctor(_)) = Functional.id
  Functor.[∘]-preserving(identityFunctor(_)) = [≡]-intro
  Functor.id-preserving (identityFunctor(_)) = [≡]-intro

{- TODO: May have to use an alternative equality definition for the proofs to work? When are two instances of Category equal?
module _  where
  open Relator.Equals

  categoryCategory : ∀{ℓₒ ℓₘ}{Obj}{_⟶_} → Category{_}{_} {Category{ℓₒ}{ℓₘ} {Obj} (_⟶_)} (Functor)
  Category._∘_           (categoryCategory) = compositionFunctor
  Category.id            (categoryCategory) {cat} = identityFunctor (cat)
  Category.identityₗ     (categoryCategory) = [≡]-intro
  Category.identityᵣ     (categoryCategory) = [≡]-intro
  Category.associativity (categoryCategory) = [≡]-intro
-}

module _
  {ℓₒ₁ ℓₘ₁ ℓₒ₂ ℓₘ₂ : Lvl.Level}
  {Obj₁ : Set(ℓₒ₁)}
  {Obj₂ : Set(ℓₒ₂)}
  {_⟶₁_ : Obj₁ → Obj₁ → Set(ℓₘ₁)}
  {_⟶₂_ : Obj₂ → Obj₂ → Set(ℓₘ₂)}
  {Category₁ : Category {_}{_} {Obj₁} _⟶₁_}
  {Category₂ : Category {_}{_} {Obj₂} _⟶₂_}
  where

  open Category
  open Functor

  private
    _∘₁_ = _∘_ (Category₁)
    _∘₂_ = _∘_ (Category₂)

    id₁ = id (Category₁)
    id₂ = id (Category₂)

  module _ where
    open Relator.Equals{ℓₘ₂}

    record NaturalTransformation
        (F₁ : Functor Category₁ Category₂)
        (F₂ : Functor Category₁ Category₂)
      : Set((ℓₒ₁ Lvl.⊔ ℓₘ₁) Lvl.⊔ (ℓₒ₂ Lvl.⊔ ℓₘ₂))
      where

      private
        functor₁ = functor (F₁)
        functor₂ = functor (F₂)

        map₁ = map (F₁)
        map₂ = map (F₂)

      field
        component : (x : Obj₁) → (functor₁(x) ⟶₂ functor₂(x))

      field
        ⦃ .proof ⦄ : ∀{x y : Obj₁}{f : x ⟶₁ y} → (component(y) ∘₂ map₁(f) ≡ map₂(f) ∘₂ component(x))

    open NaturalTransformation

    NaturalTransformation-id : ∀{F : Functor Category₁ Category₂} → NaturalTransformation(F)(F)
    component (NaturalTransformation-id{F}) (_) = id₂
    proof     (NaturalTransformation-id{F}) {x}{y}{f} rewrite identityₗ (Category₂) {functor(F)(x)}{functor(F)(y)}{map(F)(f)}
                                                            | identityᵣ (Category₂) {functor(F)(x)}{functor(F)(y)}{map(F)(f)}
                                                            = [≡]-intro
      -- (component(y) ∘₂ map(f) ≡ map(f) ∘₂ component(x))
      --   component : (x : Obj₁) → (F(x) ⟶₂ F(x))
      --   component(x) = id
      -- ((id: F(y) ⟶₂ F(y)) ∘₂ map(f) ≡ map(f) ∘₂ (id: F(x) ⟶₂ F(x)))
      --   map(f) : F(x) ⟶₂ F(y)
      -- map(f) ≡ map(f)

    module _ {F G H : Functor Category₁ Category₂} (N₁ : NaturalTransformation(G)(H)) (N₂ : NaturalTransformation(F)(G)) where
      private
        η₁ = component(N₁)
        η₂ = component(N₂)

      NaturalTransformation-composition : NaturalTransformation(F)(H)
      component (NaturalTransformation-composition) (x) = η₁(x) ∘₂ η₂(x)
      proof     (NaturalTransformation-composition) {x}{y}{f} rewrite associativity (Category₂) {_}{_}{_}{_} {η₁(y)}     {η₂(y)}     {map(F)(f)}
                                                                    | proof(N₂) {x}{y}{f}
        = symmetry(associativity (Category₂) {_}{_}{_}{_} {η₁(y)}     {map(G)(f)} {η₂(x)})
          🝖 [≡]-with(_∘₂ η₂(x)) (proof(N₁) {x}{y}{f})
          🝖 associativity (Category₂) {_}{_}{_}{_} {map(H)(f)} {η₁(x)}     {η₂(x)}
        -- For x: Obj₁ , y: Obj₁ , f: x ⟶₁ y
        -- Assumptions:
        -- • η₁(y) ∘₂ mapG(f) ≡ mapH(f) ∘₂ η₁(x) //[1]:
        -- • η₂(y) ∘₂ mapF(f) ≡ mapG(f) ∘₂ η₂(x) //[2]:
        -- Conclusion:
        -- • (η₁(y) ∘₂ η₂(y)) ∘₂ mapF(f) ≡ mapH(f) ∘₂ (η₁(x) ∘₂ η₂(x))
        --   η₁(y) ∘₂ mapG(f) ≡ mapH(f) ∘₂ η₁(x) //[1]
        --   (η₁(y) ∘₂ mapG(f)) ∘₂ η₂(x) ≡ (mapH(f) ∘₂ η₁(x)) ∘₂ η₂(x)
        --   η₁(y) ∘₂ (mapG(f) ∘₂ η₂(x)) ≡ (mapH(f) ∘₂ η₁(x)) ∘₂ η₂(x)
        --   η₁(y) ∘₂ (η₂(y) ∘₂ mapF(f)) ≡ (mapH(f) ∘₂ η₁(x)) ∘₂ η₂(x) //[2]
        --   (η₁(y) ∘₂ η₂(y)) ∘₂ mapF(f) ≡ (mapH(f) ∘₂ η₁(x)) ∘₂ η₂(x)
        --   (η₁(y) ∘₂ η₂(y)) ∘₂ mapF(f) ≡ mapH(f) ∘₂ (η₁(x) ∘₂ η₂(x))

  {-
  module _ where
    open Relator.Equals

    open NaturalTransformation

    functorCategory : Category{_}{_} {Functor Category₁ Category₂} (NaturalTransformation)
    _∘_           (functorCategory) = NaturalTransformation-composition
    id            (functorCategory) = NaturalTransformation-id
    identityₗ     (functorCategory) {F}{G} {N} rewrite identityₗ (Category₂) {_}{_} {id₂} = [≡]-intro
      -- For x: Functor(Category₁) (Category₂) , y: Functor(Category₁) (Category₂) , f: NaturalTransformation(x)(y)
      --
      -- NaturalTransformation-id ∘ f
      -- ≡ x ↦ component(NaturalTransformation-id)(x) ∘₂ component(f)(x)
      -- ≡ x ↦ id₂ ∘₂ component(f)(x)
      -- ≡ x ↦ component(f)(x)
      -- ≡ f
    identityᵣ     (functorCategory) = [≡]-intro
    associativity (functorCategory) = [≡]-intro
  -}

module _ {ℓ} where
  open import Structure.Operator.Monoid{Lvl.𝟎}{ℓ}

  monoidCategory : ∀{T : Set(ℓ)}{_▫_ : T → T → T} → Monoid{T}(_▫_) → Category{Lvl.𝟎}{ℓ} {Unit}(const(const(T)))
  Category._∘_           (monoidCategory{_}{_▫_}(M)) {_}{_}{_} = (_▫_)
  Category.id            (monoidCategory{_}{_▫_}(M)) {_} = Monoid.id(M)
  Category.identityₗ     (monoidCategory{_}{_▫_}(M)) {_}{_} = Monoid.identityₗ(M)
  Category.identityᵣ     (monoidCategory{_}{_▫_}(M)) {_}{_} = Monoid.identityᵣ(M)
  Category.associativity (monoidCategory{_}{_▫_}(M)) {_}{_}{_}{_} = Monoid.associativity(M)
