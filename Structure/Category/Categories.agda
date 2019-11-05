module Structure.Category.Categories where

open import Data
open import Functional
import      Lvl
open import Sets.Setoid
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.Functor.Functors
open import Structure.Category.Proofs
open import Structure.Operator.Properties
open import Type

module _ {ℓₒ ℓₘ} where
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equivalence

  -- The empty category is a category containing nothing.
  -- The objects are empty.
  -- The morphisms are empty.
  emptyCategory : Category{ℓₒ}{ℓₘ}{Obj = Empty}(empty)
  Category._∘_           (emptyCategory) {}
  Category.id            (emptyCategory) {}
  Category.identityₗ     (emptyCategory) {}
  Category.identityᵣ     (emptyCategory) {}
  Category.associativity (emptyCategory) {}

module _ {ℓₒ ℓₘ} where
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equivalence

  -- The single category is a category containing a single object.
  -- The objects consists of a single thing.
  -- The morphisms consists of a single connection connecting the single thing to itself.
  singleCategory : Category{ℓₒ}{ℓₘ}{Obj = Unit}(const(const Unit))
  Category._∘_                      (singleCategory) <> <> = <>
  Category.id                       (singleCategory) = <>
  Identityₗ.proof(Category.identityₗ (singleCategory)) = [≡]-intro
  Identityᵣ.proof(Category.identityᵣ (singleCategory)) = [≡]-intro
  Category.associativity            (singleCategory) = [≡]-intro


{- TODO: May have to use an alternative equality definition for the proofs to work? When are two instances of Category equal?

Can some of these be used:
• https://en.wikipedia.org/wiki/Isomorphism_of_categories
• https://en.wikipedia.org/wiki/Equivalence_of_categories
?
-}

{- TODO: First define an equivalence of functors. That would assume an equivalence of its category's objects and morphisms
module _
  {ℓₒ ℓₘ : Lvl.Level}
  {Obj : Type{ℓₒ}}
  {Morphism : Obj → Obj → Type{ℓₘ}}
  ⦃ morphism-equiv : ∀{x y} → Equiv(Morphism x y) ⦄
  where

  -- Category-equiv : Equiv(Category{ℓₒ}{ℓₘ} {Obj} (Morphism))
  categoryCategory : Category{Obj = Category{ℓₒ}{ℓₘ} {Obj} (Morphism)} (Functor)
  

  Category._∘_                       (categoryCategory) F₁ F₂ = compositionFunctor F₁ F₂
  Category.id                        (categoryCategory) = identityFunctor
  Identityₗ.proof (Category.identityₗ categoryCategory) {x} = {!!}
  Identityᵣ.proof (Category.identityᵣ categoryCategory) {x} = {!!}
  Category.associativity             (categoryCategory) {x}{y}{z}{w} {F₁}{F₂}{F₃} = {!!}

  Category-equiv = ?
-}
