module Structure.Category where

import      Lvl
open import Data
open import Functional using (const ; swap)
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid.Uniqueness
open import Sets.Setoid
import      Structure.Operator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Function
open import Type
open import Type.Unit

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

-- Obj is the collection of objects.
-- _⟶_ is the collection of morphisms.
module _ {ℓₒ ℓₘ : Lvl.Level} {Obj : Set(ℓₒ)} (Morphism : Obj → Obj → Set(ℓₘ)) where
  open Sets.Setoid.Uniqueness
  open Sets.Setoid

  module ArrowNotation where
    _⟶_ : Obj → Obj → Set(ℓₘ)
    _⟶_ = Morphism

    -- Reversed arrow
    _⟵_ : Obj → Obj → Set(ℓₘ)
    _⟵_ = swap(_⟶_)

    -- Self-pointing arrow
    ⟲_ : Obj → Set(ℓₘ)
    ⟲ a = a ⟶ a

  -- A category can be seen as an generalization of a collection of sets (the objects)
  -- and the functions between them. More specifically the algebraic rules of functions
  -- regarding composition and the identity function.
  --
  -- An alternative interpretation:
  -- A type and a binary relation on this type is a category when:
  -- • The relator is transitive.
  -- • The relator is reflexive.
  -- • The reflexivity proof inside the transitivity proof result in the same proof.
  -- • Chains of the transitivity proofs can be applied in any direction and the resulting proof will be the same.
  --
  -- When the objects are algebraic structures, the morphisms is usually homomorphisms of the respective algebraic structure.
  -- In the case of categories being the objects in a category, functors are homomorphisms, and therefore also the morphisms.
  -- TODO: https://math.stackexchange.com/questions/405459/homomorphisms-vs-functors/405479#comment867772_405459 https://ncatlab.org/nlab/show/homomorphism)
  record Category ⦃ morphism-equiv : ∀{x y} → Equiv(Morphism x y) ⦄ : Set(ℓₒ Lvl.⊔ ℓₘ) where -- TODO: A category could also be seen as an algebraic structure, but one difference from e.g. groups is that this definition also tries to generalize the notion of functions as elements of the algebraic structure
    open ArrowNotation

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
      -- ∀{x y : Obj}{f : x ⟶ y} → (id ∘ f ≡ f)
      ⦃ identityₗ ⦄ : ∀{x y : Obj} → Names.Identityₗ {T₂ = x ⟶ y} (_∘_)(id)

      -- The morphism `id` behaves like a right identity element with respect to the binary operator.
      -- Applying the proof of reflexivity on transitivity to the right is an identity function for proofs.
      -- ∀{x y : Obj}{f : x ⟶ y} → (f ∘ id ≡ f)
      ⦃ identityᵣ ⦄ : ∀{x y : Obj} → Names.Identityᵣ {T₁ = x ⟶ y} (_∘_)(id)

      -- The binary operator on mophisms is associative.
      -- The order of applying two transitivies on three proofs does not matter. It is the same proof.
      -- ∀{x y z w : Obj}{f : y ⟶ x}{g : z ⟶ y}{h : w ⟶ z} → ((f ∘ g) ∘ h ≡ f ∘ (g ∘ h))
      ⦃ associativity ⦄ : ∀{x y z w : Obj} → Names.AssociativityPattern {T₁ = y ⟶ x} {T₂ = z ⟶ y} {T₃ = w ⟶ z} (_∘_)(_∘_)(_∘_)(_∘_)

    -- The domain of a morphism
    dom : ∀{x y : Obj} → (x ⟶ y) → Obj
    dom{x}{y} (f) = x

    -- The codomain of a morphism
    codom : ∀{x y : Obj} → (x ⟶ y) → Obj
    codom{x}{y} (f) = y

    -- A morphism is an isomorphism when it has an inverse with respect to the operator.
    -- For the set and functions category, it means that f is bijective.
    Isomorphism : ∀{x y} → (x ⟶ y) → Stmt
    Isomorphism(f) = ∃(g ↦ (g ∘ f ≡ id)∧(f ∘ g ≡ id))

    -- A morphism is an endomorphism when the domain and the codomain are equal.
    -- Something which morphs itself (referring to the object).
    Endomorphism : ⦃ _ : Equiv(Obj) ⦄ → ∀{x y} → (x ⟶ y) → Stmt
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
    inverseₗ : ∀{x y}{f : x ⟶ y} → ⦃ iso : Isomorphism(f) ⦄ → ((inv f ⦃ iso ⦄) ∘ f ≡ id)
    inverseₗ ⦃ proof ⦄ = [∧]-elimₗ([∃]-proof(proof))

    -- Proof that the inverse actually is a right inverse.
    inverseᵣ : ∀{x y}{f : x ⟶ y} → ⦃ iso : Isomorphism(f) ⦄ → (f ∘ (inv f ⦃ iso ⦄) ≡ id)
    inverseᵣ ⦃ proof ⦄ = [∧]-elimᵣ([∃]-proof(proof))

    -- Proposition stating that two objects are isomorphic.
    Isomorphic : Obj → Obj → Stmt
    Isomorphic(x)(y) = ∃(Isomorphism{x}{y})

    -- An initial object is an object in which there is an unique morphism from it to every object.
    InitialObject : Obj → Stmt
    InitialObject(x) = (∀{y} → IsUnit(x ⟶ y))

    -- An terminal object is an object in which there is an unique morphism to it from every object.
    TerminalObject : Obj → Stmt
    TerminalObject(y) = (∀{x} → IsUnit(x ⟶ y))
