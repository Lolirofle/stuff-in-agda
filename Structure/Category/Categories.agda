module Structure.Category.Categories where

open import Data
open import Data.Proofs
open import Data.Tuple as Tuple using ()
open import Functional
open import Logic
import      Lvl
open import Structure.Setoid
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.Functor.Functors
open import Structure.Category.Proofs
open import Structure.Category.Properties
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level

-- The empty category is a category containing nothing.
-- The objects are empty.
-- The morphisms are empty.
emptyCategory : Category{ℓ₁}{ℓ₂}(empty) ⦃ \{} ⦄
Category._∘_            emptyCategory {}
Category.id             emptyCategory {}
Category.binaryOperator emptyCategory {}
Morphism.Associativity.proof (Category.associativity emptyCategory) {}
Morphism.Identityₗ.proof (Tuple.left  (Category.identity emptyCategory)) {}
Morphism.Identityᵣ.proof (Tuple.right (Category.identity emptyCategory)) {}

{-
module _ where
  private variable _▫_ : Unit{ℓ₁} → Unit{ℓ₁} → Stmt{ℓ₂}

  module _ ⦃ proof : (<> ▫ <>) ⦄ ⦃ equiv : Equiv(<> ▫ <>) ⦄ where
    -- The single category is a category containing a single object.
    -- The objects consists of a single thing.
    -- The morphisms consists of a single connection connecting the single thing to itself.
    singleCategory : Category{Obj = Unit}(_▫_) ⦃ equiv ⦄
    Category._∘_ singleCategory {<>} {<>} {<>} p q = {!q!}
    Category.id singleCategory {<>} = {!!}
    BinaryOperator.congruence (Category.binaryOperator singleCategory) _ _ = reflexivity(_) ⦃ Equivalence.reflexivity (Equiv.equivalence(equiv)) ⦄
    Morphism.Associativity.proof (Category.associativity singleCategory) = reflexivity(_) ⦃ Equivalence.reflexivity (Equiv.equivalence(equiv)) ⦄
    Morphism.Identityₗ.proof (Tuple.left (Category.identity singleCategory)) {<>} {<>} = {!reflexivity(_) ⦃ Equivalence.reflexivity (Equiv.equivalence(equiv)) ⦄!}
    Morphism.Identityᵣ.proof (Tuple.right (Category.identity singleCategory)) = {!!}
  -- reflexivity(_≡_) ⦃ Equivalence.reflexivity (Equiv.equivalence equiv) ⦄
-}

{- 

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
-}
