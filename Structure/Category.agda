module Structure.Category where

import      Lvl
open import Data
open import Functional using (const ; swap)
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid.Uniqueness
open import Sets.Setoid
import      Structure.Operator.Names as Names
import      Structure.Operator.Properties as Properties
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Function
open import Type
open import Type.Unit

-- Obj is the collection of objects.
-- _⟶_ is the collection of morphisms.
module _ {ℓₒ ℓₘ : Lvl.Level} {Obj : Type{ℓₒ}} (Morphism : Obj → Obj → Type{ℓₘ}) where

  -- A morphism is an endomorphism when the domain and the codomain are equal.
  -- Something which morphs itself (referring to the object).
  Endomorphism : Obj → Stmt{ℓₘ}
  Endomorphism a = Morphism a a

  module ArrowNotation where
    _⟶_ : Obj → Obj → Type{ℓₘ}
    _⟶_ = Morphism

    -- Reversed arrow
    _⟵_ : Obj → Obj → Type{ℓₘ}
    _⟵_ = swap(_⟶_)

    -- Self-pointing arrow
    ⟲_ : Obj → Type{ℓₘ}
    ⟲_ = Endomorphism

  module Morphism where
    -- The domain of a morphism
    dom : ∀{x y : Obj} → Morphism(x)(y) → Obj
    dom{x}{y} (f) = x

    -- The codomain of a morphism
    codom : ∀{x y : Obj} → Morphism(x)(y) → Obj
    codom{x}{y} (f) = y

  module Object ⦃ morphism-equiv : ∀{x y} → Equiv(Morphism x y) ⦄ where
    -- An initial object is an object in which there is an unique morphism from it to every object.
    Initial : Obj → Stmt
    Initial(x) = (∀{y} → IsUnit(Morphism x y))

    -- An terminal object is an object in which there is an unique morphism to it from every object.
    Terminal : Obj → Stmt
    Terminal(y) = (∀{x} → IsUnit(Morphism x y))

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
  record Category ⦃ morphism-equiv : ∀{x y} → Equiv(Morphism x y) ⦄ : Stmt{ℓₒ Lvl.⊔ ℓₘ} where -- TODO: A category could also be seen as an algebraic structure, but one difference from e.g. groups is that this definition also tries to generalize the notion of functions as elements of the algebraic structure
    open ArrowNotation

    field
      -- Existence of morphisms constructed by connecting two morphisms (The composition of two morphisms).
      -- Existence of a binary operator on morphisms connecting the ends of two morphisms.
      -- Proof of transitivity for the binary relator (_⟶_).
      -- Note that this is the operator like the operators in other algebraic structures with binary operators
      -- ∀{x y z : Obj} → (y ⟶ z) → (x ⟶ y) → (x ⟶ z)
      _∘_ : Names.SwappedTransitivity(_⟶_)

      -- Existence of a morphism connected to itself (The identity morphism).
      -- Proof of reflexivity for the binary relator (_⟶_).
      -- ∀{x : Obj} → (x ⟶ x)
      id  : Names.Reflexivity(_⟶_)

    field
      -- The morphism `id` behaves like a left identity element with respect to the binary operator.
      -- Applying the proof of reflexivity on transitivity to the left is an identity function for proofs.
      -- ∀{x y : Obj}{f : x ⟶ y} → (id ∘ f ≡ f)
      ⦃ identityₗ ⦄ : ∀{x y : Obj} → Properties.Identityₗ {T₂ = x ⟶ y} (_∘_)(id)

      -- The morphism `id` behaves like a right identity element with respect to the binary operator.
      -- Applying the proof of reflexivity on transitivity to the right is an identity function for proofs.
      -- ∀{x y : Obj}{f : x ⟶ y} → (f ∘ id ≡ f)
      ⦃ identityᵣ ⦄ : ∀{x y : Obj} → Properties.Identityᵣ {T₁ = x ⟶ y} (_∘_)(id)

      -- The binary operator on mophisms is associative.
      -- The order of applying two transitivies on three proofs does not matter. It is the same proof.
      -- ∀{x y z w : Obj}{f : y ⟶ x}{g : z ⟶ y}{h : w ⟶ z} → ((f ∘ g) ∘ h ≡ f ∘ (g ∘ h))
      ⦃ associativity ⦄ : ∀{x y z w : Obj} → Names.AssociativityPattern {T₁ = y ⟶ x} {T₂ = z ⟶ y} {T₃ = w ⟶ z} (_∘_)(_∘_)(_∘_)(_∘_)

    -- A morphism is an isomorphism when it is invertible with respect to the operator.
    -- For the set and functions category, it means that f is bijective.
    module _ {x y : Obj} (f : x ⟶ y) where
      record Isomorphism : Stmt{ℓₘ} where
        constructor intro
        field
          -- The inverse of f (proof of existence of an inverse)
          inv : y ⟶ x

        field
          -- Proof that inv is the left inverse of f
          inverseₗ : (inv ∘ f ≡ id)

          -- Proof that inv is the right inverse of f
          inverseᵣ : (f ∘ inv ≡ id)

      inv = inst-fn Isomorphism.inv

      inverseₗ : ⦃ iso : _ ⦄ → type-of (Isomorphism.inverseₗ (iso))
      inverseₗ ⦃ iso ⦄ = Isomorphism.inverseₗ (iso)

      inverseᵣ : ⦃ iso : _ ⦄ → type-of (Isomorphism.inverseᵣ (iso))
      inverseᵣ ⦃ iso ⦄ = Isomorphism.inverseᵣ (iso)

      -- A morphism is an monomorphism when it is left-cancellable ("injective").
      -- ∀{z}{g₁ g₂ : z ⟶ x} → (f ∘ g₁ ≡ f ∘ g₂) → (g₁ ≡ g₂)
      record Monomorphism : Stmt{ℓₒ Lvl.⊔ ℓₘ} where
        constructor intro
        field
          proof : ∀{z} → Names.CancellationOnₗ {T₂ = z ⟶ x} (_∘_) (f)
      cancellationₗ = inst-fn Monomorphism.proof

      -- A morphism is an epimorphism when it is right-cancellable ("surjective").
      -- ∀{z}{g₁ g₂ : y ⟶ z} → (g₁ ∘ f ≡ g₂ ∘ f) → (g₁ ≡ g₂)
      record Epimorphism : Stmt{ℓₒ Lvl.⊔ ℓₘ} where
        constructor intro
        field
          proof : ∀{z} → Names.CancellationOnᵣ {T₁ = y ⟶ z} (_∘_) (f)
      cancellationᵣ = inst-fn Epimorphism.proof

    -- Proposition stating that two objects are isomorphic.
    Isomorphic : Obj → Obj → Stmt
    Isomorphic(x)(y) = ∃(Isomorphism{x}{y})

    -- A morphism is an automorphism when it is an endomorphism and an isomorphism.
    Automorphism : ∀{x} → (⟲ x) → Stmt
    Automorphism = Isomorphism
