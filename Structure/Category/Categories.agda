module Structure.Category.Categories where

open import Data
open import Data.Proofs
open import Functional
open import Logic
import      Lvl
import      Relator.Equals as Eq
open import Structure.Setoid.WithLvl
open import Structure.Category
open import Structure.Categorical.Proofs
open import Structure.Categorical.Properties
open import Structure.Operator
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ : Lvl.Level
private variable Obj A B : Type{ℓ}
private variable _▫_ : Obj → Obj → Type{ℓ}
private variable f : A → B

-- The empty category is a category containing nothing.
-- The objects are empty.
-- The morphisms are empty.
emptyCategory : Category{ℓ₁}{ℓ₂}{ℓₑ}(empty-morphism) ⦃ \{} ⦄
Category._∘_            emptyCategory = empty-comp
Category.id             emptyCategory = empty-id
Category.binaryOperator emptyCategory {}
Category.associativity  emptyCategory = empty-associativity ⦃ \{} ⦄
Category.identity       emptyCategory = empty-identity ⦃ \{} ⦄

-- The single category is a category containing a single object and a single morphism.
-- The objects consists of a single thing.
-- The morphisms consists of a single connection connecting the single thing to itself.
singleCategory : ∀{ℓₒ ℓᵢ ℓₚₐ₁ ℓₚₐ₂ ℓₚᵢ₁ ℓₚᵢ₂ ℓₚᵢ₃ : Lvl.Level} → Category{ℓ₁}{ℓ₂}(single-morphism)
Category._∘_ (singleCategory{ℓ₁}{ℓ₂}{ℓₒ}{ℓᵢ}{ℓₚₐ₁}{ℓₚₐ₂}{ℓₚᵢ₁}{ℓₚᵢ₂}{ℓₚᵢ₃}) = single-comp{ℓ₂}{ℓₒ}
Category.id  (singleCategory{ℓ₁}{ℓ₂}{ℓₒ}{ℓᵢ}{ℓₚₐ₁}{ℓₚₐ₂}{ℓₚᵢ₁}{ℓₚᵢ₂}{ℓₚᵢ₃}) = single-id{ℓ₂}{ℓᵢ}
BinaryOperator.congruence (Category.binaryOperator singleCategory) Eq.[≡]-intro Eq.[≡]-intro = Eq.[≡]-intro
Category.associativity (singleCategory{ℓ₁}{ℓ₂}{ℓₒ}{ℓᵢ}{ℓₚₐ₁}{ℓₚₐ₂}{ℓₚᵢ₁}{ℓₚᵢ₂}{ℓₚᵢ₃}) = single-associativity{ℓ₂}{ℓ₂}{ℓₚₐ₁}{ℓ₁}{ℓₚₐ₂}
Category.identity      (singleCategory{ℓ₁}{ℓ₂}{ℓₒ}{ℓᵢ}{ℓₚₐ₁}{ℓₚₐ₂}{ℓₚᵢ₁}{ℓₚᵢ₂}{ℓₚᵢ₃}) = single-identity{ℓ₂}{ℓ₂}{ℓₚᵢ₁}{ℓ₁}{ℓₚᵢ₂}{ℓₚᵢ₃}

on₂-category : ⦃ morphism-equiv : ∀{x y} → Equiv{ℓₑ}(x ▫ y) ⦄ → Category{Obj = B}(_▫_) ⦃ morphism-equiv ⦄ → (f : A → B) → Category((_▫_) on₂ f)
Category._∘_ (on₂-category C _) = Category._∘_ C
Category.id  (on₂-category C _) = Category.id  C
BinaryOperator.congruence (Category.binaryOperator (on₂-category C _)) = BinaryOperator.congruence(Category.binaryOperator C)
Category.associativity (on₂-category C f) = on₂-associativity f (Category.associativity C)
Category.identity      (on₂-category C f) = on₂-identity f (Category.identity C)

{- 
TODO:
• https://en.wikipedia.org/wiki/Isomorphism_of_categories
• https://en.wikipedia.org/wiki/Equivalence_of_categories
?
-}
