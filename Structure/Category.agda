import      Lvl

-- Obj is the collection of objects.
-- _⟶_ is the collection of morphisms.
module Structure.Category {ℓₒ ℓₘ ℓₑ : Lvl.Level} where

open import Data
open import Functional using (const ; swap)
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid.Uniqueness
import      Structure.Category.Names as Names
open import Structure.Category.Properties as Properties
import      Structure.Operator.Names as Names
open import Structure.Operator
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Structure.Setoid.WithLvl
open import Syntax.Function
open import Type.Unit
open import Type

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
  -- An alternative interpretation of the definition:
  -- A type (Obj) and a binary relation (Morphism) on this type is a category when:
  -- • The relator is transitive.
  -- • The relator is reflexive.
  -- • The reflexivity proof inside the transitivity proof does not result in a new proof.
  -- • Chains of the transitivity proofs can be applied in any order and the resulting proof will be the same.
  --
  -- A more concrete interpretation of the binary relation one is that a category describes a graph.
  -- Vertices are objects and morphisms are paths between the vertices.
  -- The operator joins two paths into one, and the identity is a loop (the empty path).
  -- See `Graph.Category`.
  --
  -- When the objects are algebraic structures, the morphisms is usually homomorphisms of the respective algebraic structure.
  -- In the case of categories being the objects in a category, functors are homomorphisms, and therefore also the morphisms.
  -- TODO: https://math.stackexchange.com/questions/405459/homomorphisms-vs-functors/405479#comment867772_405459 https://ncatlab.org/nlab/show/homomorphism)
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
      -- The order of applying two transitivies on three proofs does not matter. It is the same proof.
      -- ∀{x y z w : Obj}{f : y ⟶ x}{g : z ⟶ y}{h : w ⟶ z} → ((f ∘ g) ∘ h ≡ f ∘ (g ∘ h))
      ⦃ associativity ⦄ : Morphism.Associativity(\{x} → _∘_ {x})

      -- The morphism `id` behaves like aa identity element with respect to the binary operator.
      -- Applying the proof of reflexivity on transitivity is an identity function for proofs.
      ⦃ identity ⦄ : Morphism.Identity(_∘_)(\{x} → id{x})

    instance
      identityₗ : Morphism.Identityₗ(_∘_)(\{x} → id{x})
      identityₗ = [∧]-elimₗ identity

    instance
      identityᵣ : Morphism.Identityᵣ(_∘_)(\{x} → id{x})
      identityᵣ = [∧]-elimᵣ identity

    -- As stated in `id`, it can be interpreted as proof of reflexivity when `Morphism` is interpreted as a binary relation.
    morphism-reflexivity : Reflexivity(_⟶_)
    morphism-reflexivity = intro id

    -- As stated in `_∘_`, it can be interpreted as proof of transitivity when `Morphism` is interpreted as a binary relation.
    morphism-transitivity : Transitivity(_⟶_)
    morphism-transitivity = intro(swap(_∘_))

    module ArrowNotation = Names.ArrowNotation(_⟶_)

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
