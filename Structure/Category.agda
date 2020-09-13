import      Lvl

module Structure.Category {ℓₒ ℓₘ ℓₑ : Lvl.Level} where

open import Functional using (swap)
open import Logic
open import Logic.Propositional
import      Structure.Categorical.Names as Names
open import Structure.Categorical.Properties
open import Structure.Semicategory{ℓₒ}{ℓₘ}{ℓₑ}
open import Structure.Operator
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Structure.Setoid.WithLvl
open import Type

-- Obj is the collection of objects.
-- _⟶_ is the collection of morphisms.
module _
  {Obj : Type{ℓₒ}}
  (_⟶_ : Obj → Obj → Type{ℓₘ})
  ⦃ morphism-equiv : ∀{x y} → Equiv{ℓₑ}(x ⟶ y) ⦄
  where

  -- A category is a structure on a relation called a morphism.
  --
  -- It can be seen as a generalization of the structure in functions between a collection of types/sets.
  -- More specifically, the algebraic properties of functions regarding composition and the identity function.
  -- In this case, sets are objects and functions are morphisms.
  -- See `Type.Category`.
  --
  -- It can also be seen as a generalized algebraic structure, or more specifically a generalization of monoids.
  -- The type of a monoid's operator is usually restricted to a single type, but a category allows it to vary (depending on the rules of morphism instead).
  -- (One can loosely call a category to be a monoid without the "closed" property of algebraic structures).
  -- In this case, the binary operation is (_∘_) and the laws are the usual identity and associative laws.
  -- See `Structure.Category.Monoid`.
  --
  -- A category can also be constructed by letting objects be the models of algebraic structures, and morphisms the homomorphisms of the respective algebraic structure.
  --
  -- In the case of categories being the objects in a category, functors are homomorphisms, and therefore also the morphisms.
  -- See `Structure.Category.Category`.
  --
  -- An alternative interpretation of the definition:
  -- A type (Obj) and a binary relation (Morphism) on this type is a category when:
  -- • The relator is transitive.
  -- • The relator is reflexive.
  -- • The reflexivity proof inside the transitivity proof does not result in a new proof.
  -- • Chains of the transitivity proofs can be applied in any order and the resulting proof will be the same.
  -- See `Relator.Equals.Category` for an example of this kind of binary relation.
  --
  -- A more concrete interpretation of the binary relation one is that a category describes a graph.
  -- Vertices are objects and morphisms are paths between the vertices.
  -- The operator joins two paths into one, and the identity is a loop (the empty path).
  -- See `Graph.Category`.
  --
  -- A category is the common pattern seen in all the examples above.
  record Category : Stmt{ℓₒ Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
    field
      -- Existence of morphisms constructed by connecting two morphisms (The composition of two morphisms).
      -- Existence of a binary operator on morphisms connecting the ends of two morphisms.
      -- Also a proof of transitivity for the binary relator (_⟶_).
      -- Note that this is the operator like the operators in other algebraic structures with binary operators
      -- ∀{x y z : Obj} → (y ⟶ z) → (x ⟶ y) → (x ⟶ z)
      _∘_ : Names.SwappedTransitivity(_⟶_)

      -- Existence of a morphism connected to itself (The identity morphism).
      -- Also a proof of reflexivity for the binary relator (_⟶_).
      -- ∀{x : Obj} → (x ⟶ x)
      id  : Names.Reflexivity(_⟶_)
    infixr 20 _∘_

    field
      -- The binary operator respects the equivalence relation.
      ⦃ binaryOperator ⦄ : ∀{x y z} → BinaryOperator(_∘_ {x}{y}{z})

      -- The binary operator on mophisms is associative.
      -- Or, the order of applying two transitivies on three proofs does not matter. It is the same proof.
      -- ∀{x y z w : Obj}{f : y ⟶ x}{g : z ⟶ y}{h : w ⟶ z} → ((f ∘ g) ∘ h ≡ f ∘ (g ∘ h))
      ⦃ associativity ⦄ : Morphism.Associativity(\{x} → _∘_ {x})

      -- The morphism `id` behaves like aa identity element with respect to the binary operator.
      -- Or, applying the proof of reflexivity on transitivity is an identity function for proofs.
      ⦃ identity ⦄ : Morphism.Identity(_∘_)(\{x} → id{x})

    instance
      identityₗ : Morphism.Identityₗ(_∘_)(\{x} → id{x})
      identityₗ = [∧]-elimₗ identity

    instance
      identityᵣ : Morphism.Identityᵣ(_∘_)(\{x} → id{x})
      identityᵣ = [∧]-elimᵣ identity

    -- As stated in `id`, this can be interpreted as proof of reflexivity when `Morphism` is interpreted as a binary relation.
    morphism-reflexivity : Reflexivity(_⟶_)
    morphism-reflexivity = intro id

    semicategory : Semicategory(_⟶_)
    Semicategory._∘_ semicategory = _∘_
    Semicategory.binaryOperator semicategory = binaryOperator
    Semicategory.associativity semicategory = associativity

    open Semicategory(semicategory) hiding (_∘_ ; binaryOperator ; associativity) public

-- A category object can be used when one refers to a category as an object.
-- Examples of usage are in functors (morphism between categories) or in equivalences of categories.
record CategoryObject : Stmt{Lvl.𝐒(ℓₒ Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    {Object}           : Type{ℓₒ}
    {Morphism}         : Object → Object → Type{ℓₘ}
    ⦃ morphism-equiv ⦄ : ∀{x y} → Equiv{ℓₑ}(Morphism x y)
    category           : Category(Morphism)

  instance
    category-instance = category
